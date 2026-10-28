"""Bounded backward retrieval of restricted plans from compiler type DAGs.

This is a proposer, not a Lean unifier or proof checker. In particular universe
levels and metadata are intentionally ignored for retrieval. The native worker
rechecks the complete original types, instances, source and proof dependencies.
No string from an inventory becomes Lean source. Search exhaustion describes
only this recorded grammar, menu and resource budget.
"""
from __future__ import annotations

from dataclasses import dataclass
from contextvars import ContextVar
import time
from .canonical import require, digest, canonical_bytes, ContractError
from .inventory import expression_hash


class _ResourceStop(Exception):
    pass


_WORK=ContextVar('opica_retrieval_work',default=None)


def _work():
    guard=_WORK.get()
    if guard is not None:
        guard['used']+=1
        if guard['used']>guard['maximum'] or time.monotonic()>guard['deadline']:
            raise _ResourceStop


def _name(value):
    if value[0] == "anonymous":
        return ""
    prefix = _name(value[1])
    return (prefix + "." if prefix else "") + value[2]


def decode(expression, maximum=100000, proof_constants=()):
    """Decode a validated DAG with sharing, never an exponential tree walk."""
    expression_hash(expression)
    require(len(expression["nodes"]) <= maximum, "retrieval DAG budget exceeded")
    rows = []
    proofs = frozenset(proof_constants)
    for node in expression["nodes"]:
        _work()
        tag = node[0]
        if tag == "mdata":
            term = rows[int(node[2])]
        elif tag == "const":
            name = _name(node[1])
            term = ("proof",) if name in proofs else ("const", name)
        elif tag == "sort":
            term = ("sort",)  # The kernel, not retrieval, checks universe levels.
        elif tag == "bvar":
            term = ("bvar", int(node[1]))
        elif tag == "app":
            function = rows[int(node[1])]
            term = ("proof",) if function[0] == "proof" else ("app", function, rows[int(node[2])])
        elif tag in {"forall", "lam"}:
            term = (tag, node[2], rows[int(node[3])], rows[int(node[4])])
        elif tag == "let":
            term = (tag, rows[int(node[2])], rows[int(node[3])], rows[int(node[4])])
        elif tag == "proj":
            term = (tag, _name(node[1]), node[2], rows[int(node[3])])
        else:
            # Literals remain rigid. Unsupported syntax cannot gain authority.
            term = ("literal", canonical_bytes(node).decode("utf8"))
        rows.append(term)
    return rows[int(expression["root"])]


def _walk(term, fn, depth=0, _memo=None):
    if _memo is None:
        _memo = {}
    key = (id(term), depth)
    if key in _memo:
        return _memo[key]
    _work()
    replacement = fn(term, depth)
    if replacement is not None:
        _memo[key] = replacement
        return replacement
    tag = term[0]
    if tag == "app":
        result = (tag, _walk(term[1], fn, depth, _memo), _walk(term[2], fn, depth, _memo))
    elif tag in {"forall", "lam"}:
        result = (tag, term[1], _walk(term[2], fn, depth, _memo), _walk(term[3], fn, depth+1, _memo))
    elif tag == "let":
        result = (tag, _walk(term[1], fn, depth, _memo), _walk(term[2], fn, depth, _memo), _walk(term[3], fn, depth+1, _memo))
    elif tag == "proj":
        result = (*term[:3], _walk(term[3], fn, depth, _memo))
    else:
        result = term
    _memo[key] = result
    return result


def _lift(term, amount, cutoff=0):
    return _walk(term, lambda t, d: ("bvar", t[1]+amount)
                 if t[0] == "bvar" and t[1] >= cutoff+d else None)


def instantiate(body, value):
    def replace(term, depth):
        if term[0] != "bvar":
            return None
        if term[1] == depth:
            return _lift(value, depth)
        if term[1] > depth:
            return ("bvar", term[1]-1)
        return term
    return _walk(body, replace)


def _head(term):
    args = []
    while term[0] == "app":
        args.append(term[2]); term = term[1]
    return term, tuple(reversed(args))


def _resolve(term, substitution, _memo=None):
    # Compiler types share large instance subexpressions. Preserve that DAG
    # while applying a fixed substitution; recursive tree expansion is not a
    # meaningful search step and can otherwise dominate the bounded search.
    if _memo is None:
        _memo = {}
    if id(term) in _memo:
        return _memo[id(term)][1]
    _work()
    if term[0] == "meta" and term[1] in substitution:
        result = _resolve(substitution[term[1]], substitution, _memo)
    elif term[0] == "app":
        f, x = _resolve(term[1], substitution, _memo), _resolve(term[2], substitution, _memo)
        if f[0] == "lam":
            result = _resolve(instantiate(f[3], x), substitution, _memo)
        else:
            result = ("app", f, x)
    elif term[0] == "let":
        result = _resolve(instantiate(term[3], term[2]), substitution, _memo)
    elif term[0] in {"forall", "lam"}:
        result = (term[0], term[1], _resolve(term[2], substitution, _memo), _resolve(term[3], substitution, _memo))
    else:
        result = term
    _memo[id(term)] = (term, result)
    return result


def _fingerprint(term, memo=None):
    """Linear in the shared expression, including rigid local identities."""
    if memo is None:
        memo = {}
    if id(term) not in memo:
        _work()
        import hashlib
        parts=[_fingerprint(x,memo) if isinstance(x,tuple) else str(x) for x in term]
        memo[id(term)] = hashlib.sha256(canonical_bytes(parts)).hexdigest()
    return memo[id(term)]


def _occurs(index, term, substitution):
    found = False
    def visit(value, _depth):
        nonlocal found
        if value[0] == "meta":
            resolved = _resolve(value, substitution)
            if resolved[0] == "meta":
                found |= resolved[1] == index
            else:
                _walk(resolved, visit)
        return None
    _walk(term, visit)
    return found


def _same(left, right):
    """Structural DAG equality without unfolding sharing into a tree."""
    pending=[(left,right)];seen=set()
    while pending:
        _work()
        a,b=pending.pop()
        if a is b:
            continue
        key=(id(a),id(b))
        if key in seen:
            continue
        seen.add(key)
        if not isinstance(a,tuple) or not isinstance(b,tuple):
            if a != b:return False
        elif len(a)!=len(b):
            return False
        else:
            pending.extend(zip(a,b))
    return True


def unify(left, right, substitution):
    _work()
    left, right = _resolve(left, substitution), _resolve(right, substitution)
    if _same(left,right):
        return True
    if left[0] == "meta":
        if _occurs(left[1], right, substitution):
            return False
        substitution[left[1]] = right
        return True
    if right[0] == "meta":
        return unify(right, left, substitution)
    if left[0] != right[0]:
        return False
    if left[0] == "app":
        return unify(left[1], right[1], substitution) and unify(left[2], right[2], substitution)
    if left[0] in {"forall", "lam"}:
        return unify(left[2], right[2], substitution) and unify(left[3], right[3], substitution)
    return False


def _closed(term):
    found = False
    def visit(value, _depth):
        nonlocal found
        found |= value[0] == "meta"
        return None
    _walk(term, visit)
    return not found


@dataclass(frozen=True)
class _Fact:
    plan: dict
    term: tuple
    type: tuple


class _Search:
    def __init__(self, constants, budget):
        self.constants = constants
        self.budget = budget
        self.states = 0
        self.next_meta = 0
        self.exhausted = False
        self.found = set()

    def tick(self):
        if self.states >= self.budget.term_nodes:
            self.exhausted = True
            return False
        self.states += 1
        return True

    def fresh(self):
        result = ("meta", self.next_meta)
        self.next_meta += 1
        return result

    def apply(self, fact, goal, locals_, depth, substitution, seen, eliminated, wanted=None, direct_only=False):
        ty = _resolve(fact.type, substitution)
        binders = []
        term = fact.term
        while ty[0] == "forall":
            if len(binders) >= self.budget.term_nodes:
                self.exhausted = True
                return
            value = self.fresh()
            binders.append((value, ty[2], ty[1]))
            term = ("app", term, value)
            ty = _resolve(instantiate(ty[3], value), substitution)
        subst = dict(substitution)
        if goal is not None and not unify(ty, goal, subst):
            return
        if wanted is not None and not unify(term, wanted, subst):
            return
        explicit = [(value, domain) for value, domain, info in binders if info == "default"]

        def arguments(index, plans, current):
            if index == len(explicit):
                out = fact.plan if not plans else {"tag":"app", "function":fact.plan, "arguments":plans}
                result_type = _resolve(ty, current)
                result_term = _resolve(term, current)
                yield _Fact(out, result_term, result_type), current
                return
            value, domain = explicit[index]
            value = _resolve(value, current)
            expected = value if value[0] != "meta" else None
            for argument, new in self.solve(_resolve(domain, current), locals_, depth+1,
                                             current, seen, eliminated, expected, facts_only=direct_only):
                updated = dict(new)
                if unify(binders_value(index), argument.term, updated):
                    yield from arguments(index+1, [*plans, argument.plan], updated)

        def binders_value(index):
            return explicit[index][0]

        yield from arguments(0, [], subst)

    def solve(self, goal, locals_, depth=0, substitution=None, seen=frozenset(),
              eliminated=frozenset(), wanted=None, facts_only=False):
        if not self.tick():
            return
        if depth > self.budget.term_depth:
            self.exhausted = True
            return
        substitution = {} if substitution is None else dict(substitution)
        goal = _resolve(goal, substitution)
        # Contexts are rigid; a same-type fact at another witness is not merged.
        fingerprints = {}
        key = (_fingerprint(goal,fingerprints), tuple(_fingerprint(f.type,fingerprints) for f in locals_),
               _fingerprint(_resolve(wanted, substitution),fingerprints) if wanted else None)
        if key in seen:
            return
        seen = seen | {key}
        if goal[0] == "forall":
            slot = len(locals_)
            local = _Fact({"tag":"local","binder_slot":slot}, ("local",slot), goal[2])
            for body, new in self.solve(instantiate(goal[3],local.term), (*locals_,local),
                                       depth+1,substitution,seen,eliminated,facts_only=facts_only):
                yield _Fact({"tag":"lambda","body":body.plan}, ("lam",goal[1],goal[2],body.term),goal), new
            return
        # Resolve direct context before spending effort on theorem applications.
        for fact in locals_:
            if not self.tick():
                return
            if fact.type[0] == "forall":
                yield from self.apply(fact,goal,locals_,depth,substitution,seen,eliminated,wanted,direct_only=facts_only)
            else:
                updated = dict(substitution)
                if unify(fact.type,goal,updated) and (wanted is None or unify(fact.term,wanted,updated)):
                    yield fact, updated
        if facts_only:
            return
        # Proved logical packets are eliminated with fresh scoped rigid locals.
        for fact in locals_:
            token = canonical_bytes(fact.plan)
            if token in eliminated:
                continue
            head, args = _head(_resolve(fact.type,substitution))
            if head not in {("const","And"),("const","Or"),("const","Exists")} or len(args)!=2:
                continue
            later = eliminated | {token}
            slot = len(locals_)
            if head == ("const","Or"):
                left = _Fact({"tag":"local","binder_slot":slot},("local",slot),args[0])
                right = _Fact({"tag":"local","binder_slot":slot},("local",slot),args[1])
                for a, s1 in self.solve(goal,(*locals_,left),depth+1,substitution,seen,later,wanted):
                    for b, s2 in self.solve(goal,(*locals_,right),depth+1,s1,seen,later,wanted):
                        yield _Fact({"tag":"cases","value":fact.plan,"branches":[a.plan,b.plan]},
                                    ("retrieved-proof",),goal), s2
            else:
                first = _Fact({"tag":"local","binder_slot":slot},("local",slot),args[0])
                second_type = args[1]
                if head == ("const","Exists"):
                    second_type = _resolve(("app",args[1],first.term),substitution)
                second = _Fact({"tag":"local","binder_slot":slot+1},("local",slot+1),second_type)
                for body, new in self.solve(goal,(*locals_,first,second),depth+1,substitution,seen,later,wanted):
                    yield _Fact({"tag":"cases","value":fact.plan,"branches":[body.plan]},
                                ("retrieved-proof",),goal), new
        # Make a shared intermediate packet by an application, then eliminate
        # it. Arbitrary opaque results are not guessed or asserted.
        # First share packets whose arguments are already supplied by the local
        # context. This avoids exhausting backward search before opening the
        # very witness packet needed by its eventual consumer. No goal-specific
        # theorem name or answer plan is involved.
        for direct_only in (True,False):
            for source in self.constants:
                result = source.type
                while result[0] == "forall":
                    result = result[3]
                head, _ = _head(result)
                if head not in {("const","And"),("const","Or"),("const","Exists")}:
                    continue
                for fact, new in self.apply(source,None,locals_,depth,substitution,seen,eliminated,direct_only=direct_only):
                    if not _closed(fact.type):
                        continue
                    token = canonical_bytes(fact.plan)
                    if token in eliminated:
                        continue
                    slot = len(locals_)
                    shared = _Fact({"tag":"local","binder_slot":slot},("local",slot),fact.type)
                    for body, end in self.solve(goal,(*locals_,shared),depth+1,new,seen,
                                                eliminated | {token},wanted):
                        yield _Fact({"tag":"let","value":fact.plan,"body":body.plan},
                                    ("retrieved-proof",),goal), end
            if direct_only:
                for fact in self.constants:
                    if not self.tick():return
                    yield from self.apply(fact,goal,locals_,depth,substitution,seen,eliminated,wanted)


def _retrieve(inventory, target, grammar, budget, expected_expression, statements=(), proof_constants=()):
    """Return deterministic candidates and honest bounded-search provenance."""
    from .proposals import validate_plan
    require(expression_hash(expected_expression) == target.expected_type_hash,
            "search target expression differs from independently frozen target")
    forbidden = set(grammar.excluded_declarations) | set(target.forbidden_constants or []) | {target.declaration}
    rows = {}
    for row in [*inventory.statements, *statements]:
        name = row["declaration"]
        if name not in target.allowed_constants.values() or name in forbidden:
            continue
        require(expression_hash(row["type_expression"]) == row["type_sha256"], "retrieval statement digest differs")
        if name in rows:
            require(rows[name]["type_sha256"] == row["type_sha256"] and rows[name]["module"] == row["module"],
                    "conflicting retrieval contracts")
        rows[name] = row
    proofs = set(proof_constants) | {p for row in rows.values() for p in row.get('proof_constants',[])}
    constants = [_Fact({"tag":"const","constant_id":cid},("const",name),decode(rows[name]["type_expression"],proof_constants=proofs))
                 for cid,name in sorted(target.allowed_constants.items()) if name in rows and name not in forbidden]
    ty = decode(expected_expression,proof_constants=proofs)
    locals_ = []
    while ty[0] == "forall":
        slot = len(locals_)
        local = _Fact({"tag":"local","binder_slot":slot},("local",slot),ty[2])
        locals_.append(local)
        ty = instantiate(ty[3],local.term)
    search = _Search(constants,budget)
    candidates, found = [], set()
    for fact,_ in search.solve(ty,tuple(locals_)):
        try:
            validate_plan(fact.plan,budget)
        except ContractError:
            search.exhausted = True
            continue
        key = digest(fact.plan,domain="OPICA_BOUNDED_COMPOSITION_PLAN_V1")
        if key in found:
            continue
        if len(candidates) == budget.candidates:
            search.exhausted = True
            break
        found.add(key)
        candidates.append({"action_id":key,"declaration":None,"term_plan":fact.plan,
                           "scientific_scope":"BOUNDED_TARGET_DIRECTED_RETRIEVAL_NOT_PROOF"})
    provenance = {"algorithm":"BOUNDED_BACKWARD_COMPILER_DAG_RETRIEVAL_V1",
                  "states":search.states,"maximum_states":budget.term_nodes,
                  "target_sha256":target.expected_type_hash,
                  "retrieval_statements":sorted(rows),
                  "proof_erasure_constants":sorted(proofs),
                  "stopping_reason":"RESOURCE_EXHAUSTED" if search.exhausted else "SEARCH_MENU_ENUMERATED",
                  "mathematical_exhaustiveness":False,"kernel_acceptance":False}
    return candidates, not search.exhausted, provenance


def retrieve(inventory, target, grammar, budget, expected_expression, statements=(), proof_constants=()):
    """Bound type processing as well as search states; exhaustion is OPEN."""
    guard={'used':0,'maximum':min(4000000,budget.term_nodes*2048),
           'deadline':time.monotonic()+budget.wall_seconds}
    token=_WORK.set(guard)
    try:
        try:
            rows,complete,record=_retrieve(inventory,target,grammar,budget,expected_expression,statements,proof_constants)
        except (_ResourceStop,RecursionError):
            rows,complete,record=[],False,{
                'algorithm':'BOUNDED_BACKWARD_COMPILER_DAG_RETRIEVAL_V1','states':None,
                'maximum_states':budget.term_nodes,'target_sha256':target.expected_type_hash,
                'stopping_reason':'RESOURCE_EXHAUSTED','mathematical_exhaustiveness':False,'kernel_acceptance':False}
        record['type_work_units']=guard['used'];record['maximum_type_work_units']=guard['maximum']
        return rows,complete,record
    finally:
        _WORK.reset(token)
