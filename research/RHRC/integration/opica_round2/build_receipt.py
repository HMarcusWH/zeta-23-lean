"""Source-bound native compiler exports and reproducible, scoped receipt replay.

The complete type/dependency parser adapts the frozen follow-up algorithm.
Warm compiler replay is explicitly scoped and never cold isolation or review.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from typing import Any, Mapping

try:
    from .certificate_io import InvalidCertificate, canonical_sha256, failure_envelope, load_strict_json, loads_strict_json, validate_schema
    from . import validate_contract as contract
except ImportError:
    from certificate_io import InvalidCertificate, canonical_sha256, failure_envelope, load_strict_json, loads_strict_json, validate_schema
    import validate_contract as contract

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MATHEMATICAL_MODULES = frozenset()
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_.]*\Z")
EXPRESSION_VALIDATOR = "research/RHRC/routes/R003_ccm_bridge/post290/lean_expr_dag.py"
# Frozen audit helpers are compiler tooling, not additional mathematical roots.
FACADE_BUILD_TARGETS = ("Zeta23.OPICARound2", "Zeta23.OPICARound2.All",
    "Zeta23.OPICARound2.Validation", "Zeta23.RHRC.OpicaRound2Bindings")
AUDIT_BUILD_TARGETS = ("Zeta23.RHRC.DeclarationDependencyExport",
    "Zeta23.RHRC.SourceCandidateResolution", "Zeta23.RHRC.OpicaTypeExprExport")

def require(ok, message):
    if not ok:
        raise InvalidCertificate("compiler_evidence", message)


def frozen_tool(repo: Path, relative: str, module_name: str):
    path = contract.file_at(repo, relative)
    payload = path.read_bytes()
    original = subprocess.run(["git", "-C", str(repo), "show", contract.FROZEN_COMMIT + ":" + relative],
                              capture_output=True, check=True).stdout
    require(payload == original, "Frozen evidence tool changed: " + relative)
    spec = importlib.util.spec_from_file_location(module_name, path)
    require(spec is not None and spec.loader is not None, "Evidence tool cannot be loaded")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

_EXPR_VALIDATOR = None

def validate_expression(text):
    global _EXPR_VALIDATOR
    if _EXPR_VALIDATOR is None:
        _EXPR_VALIDATOR = frozen_tool(REPO, EXPRESSION_VALIDATOR, "_opica2_frozen_expr")
    # Strict JSON rejection is separate from Lean expression semantic validation.
    loads_strict_json(text, 16 * 1024 * 1024)
    return _EXPR_VALIDATOR.validate_expression(text)

def validate_dependency_closure(declarations, metadata, dependencies):
    """Check the complete project traversal, including private helper nodes.

    Every project constant reached by the exporter is expanded in all three
    channels. External constants are boundary nodes. Checking only public root
    channels would accept a log truncated just before a helper's expansion.
    """
    public = {item['name']: item for item in declarations}
    require(len(public) == len(declarations), 'duplicate public declaration')
    nodes = {item['name']: item for item in metadata}
    require(len(nodes) == len(metadata), 'duplicate dependency declaration')
    kinds = {'AXIOM','DEFINITION','THEOREM','OPAQUE','QUOTIENT','INDUCTIVE','CONSTRUCTOR','RECURSOR'}
    for item in metadata:
        require(item['kind'] in kinds and type(item['internal']) is bool,
            'invalid dependency declaration metadata')
    def project(item):
        return item['module'] == 'Zeta23' or item['module'].startswith('Zeta23.')
    for item in metadata:
        require(item['kind'] != 'AXIOM' or (item['name'] in ALLOWED_AXIOMS and not project(item)),
                'unadmitted transitive/private axiom: '+item['name'])
    for name, item in public.items():
        require(name in nodes, 'missing public dependency metadata: '+name)
        require(nodes[name]['module'] == item['module'] and nodes[name]['kind'] == item['kind']
            and not nodes[name]['internal'], 'public dependency metadata mismatch: '+name)
    channels = {}
    for item in dependencies:
        source, channel, targets = item['source'], item['channel'], item['targets']
        require(source in nodes, 'unknown dependency source')
        require(project(nodes[source]), 'external dependency boundary was expanded: '+source)
        require(channel in {'TYPE','VALUE','STRUCTURE'}, 'unknown dependency channel')
        require((source,channel) not in channels, 'duplicate dependency channel')
        require(len(targets) == len(set(targets)) and all(targets), 'invalid dependency targets')
        require(all(target in nodes for target in targets), 'unknown dependency target')
        channels[source,channel] = targets
    for name, item in nodes.items():
        if project(item):
            require(all((name,c) in channels for c in ('TYPE','VALUE','STRUCTURE')),
                'incomplete project dependency channels: type/value/structure provenance: '+name)
    reached, pending = set(), list(public)
    while pending:
        source = pending.pop()
        if source in reached:
            continue
        reached.add(source)
        if project(nodes[source]):
            for channel in ('TYPE','VALUE','STRUCTURE'):
                pending.extend(channels[source,channel])
    require(reached == set(nodes), 'unreachable dependency metadata outside public-root closure')


def validate_compiler_records(receipt, expected_roots=(), *, mathematical_modules=None):
    """Revalidate serialized evidence without trusting its stored type hashes."""
    modules = MATHEMATICAL_MODULES if mathematical_modules is None else frozenset(mathematical_modules)
    records = receipt['declarations']
    require(isinstance(records,list) and bool(records), 'empty or malformed public declaration inventory')
    equations = receipt.get('generated_equations', {})
    require(isinstance(equations,dict) and all(isinstance(name,str) and isinstance(origin,str)
        for name,origin in equations.items()), 'malformed generated equation provenance')
    declarations = {}
    kinds = {'DEFINITION','THEOREM','OPAQUE','QUOTIENT','INDUCTIVE','CONSTRUCTOR','RECURSOR'}
    for record in records:
        require(isinstance(record,dict) and {'name','module','kind','axioms','type_expression',
            'type_sha256','type_metrics'}<=set(record), 'missing public declaration evidence fields')
        name,module,kind = record['name'],record['module'],record['kind']
        require(isinstance(name,str) and name not in declarations, 'invalid or duplicate public declaration')
        require(module in modules, 'foreign defining module')
        require(kind in kinds, 'unadmitted public declaration kind')
        require(name.startswith('Zeta23.OPICARound2.') or
            (kind=='THEOREM' and (name.endswith('.congr_simp') or name in equations)),
            'foreign declaration namespace')
        axioms = record['axioms']
        require(isinstance(axioms,list) and all(isinstance(ax,str) for ax in axioms)
            and len(axioms)==len(set(axioms)) and set(axioms)<=ALLOWED_AXIOMS,
            'unadmitted mathematical axiom: '+name)
        require(isinstance(record['type_expression'],dict), 'missing or malformed full type DAG: '+name)
        encoded = json.dumps(record['type_expression'],ensure_ascii=False,separators=(',',':'))
        metrics = validate_expression(encoded)
        digest = hashlib.sha256(encoded.encode('utf-8')).hexdigest()
        require(record['type_sha256']==digest, 'full type DAG digest mismatch: '+name)
        require(record['type_metrics']==metrics, 'full type DAG metrics mismatch: '+name)
        declarations[name] = record
    for root in expected_roots:
        require(root['full_name'].startswith('Zeta23.OPICARound2.'), 'foreign primary root namespace')
        require(root['module'] in modules, 'foreign primary defining module')
        record = declarations.get(root['full_name'])
        require(record is not None and record['module']==root['module'] and record['kind']==root['kind'],
            'missing or wrong source-bound primary declaration: '+root['full_name'])
        require(isinstance(record.get('full_type'),str) and bool(record['full_type'].strip()),
            'missing human-readable root type')
        if 'expected_type_sha256' in root:
            require(record['type_sha256']==root['expected_type_sha256'], 'reviewed expected type changed: '+root['full_name'])
    constructors = receipt.get('constructors')
    require(isinstance(constructors,dict), 'missing or malformed constructor inventory')
    require(set(constructors)=={name for name,record in declarations.items() if record['kind']=='CONSTRUCTOR'},
        'constructor inventory differs from public constructor declarations')
    validate_dependency_closure(records,receipt['dependency_declarations'],receipt['dependencies'])
    channels = {(item['source'],item['channel']):item['targets'] for item in receipt['dependencies']}
    validate_generated_equations(equations,declarations,channels,
        {row['name']:(row['module'],row['kind'],'1' if row['internal'] else '0')
            for row in receipt['dependency_declarations']})
    for node in receipt['dependency_declarations']:
        if node['module'] in modules and not node['internal']:
            require(node['name'] in declarations, 'public mathematical dependency escaped enumeration: '+node['name'])
    for name,record in constructors.items():
        family = record['family']
        require(family in declarations and declarations[family]['kind']=='INDUCTIVE', 'constructor family mismatch')
        require(isinstance(record['type_expression'],dict), 'malformed constructor full type')
        validate_expression(json.dumps(record['type_expression'],ensure_ascii=False,separators=(',',':')))
        require(record['type_expression']==declarations[name]['type_expression'], 'constructor full type mismatch')
        require(channels[name,'STRUCTURE']==[family], 'constructor structural family mismatch')
        require(name in channels[family,'STRUCTURE'], 'constructor missing from inductive structural family')


def validate_generated_equations(equations, declarations, channels, dependency_declarations):
    """Reserved equation names are audited helpers, never additional roots."""
    for name, origin in equations.items():
        require(name in declarations and declarations[name]['kind'] == 'THEOREM',
                'generated equation lacks public theorem audit')
        require(re.fullmatch(re.escape(origin) + r'\.(?:eq_[0-9]+|eq_def|eq_unfold)', name) is not None,
                'generated equation has noncanonical reserved name')
        require(origin in channels.get((name, 'TYPE'), []),
                'generated equation type does not reference its original definition')
        require(origin in dependency_declarations and dependency_declarations[origin][1] == 'DEFINITION',
                'generated equation origin is not an audited definition')


def parse_compiler_output(text, expected_roots, *, mathematical_modules=None):
    modules = MATHEMATICAL_MODULES if mathematical_modules is None else frozenset(mathematical_modules)
    declarations, constructors, candidates, channels, dependency_declarations = {}, {}, {}, {}, {}
    generated_equations = {}
    count, complete = None, None
    for root in expected_roots:
        require(root['full_name'].startswith('Zeta23.OPICARound2.'), 'foreign primary root namespace')
        require(root['module'] in modules, 'foreign primary defining module')
    for line in text.splitlines():
        require(complete is None or not line.strip(), 'output after the terminating completeness record')
        if line.startswith('OPICA2_DECL\t'):
            parts = line.split('\t')
            require(len(parts) == 6, 'malformed OPICA declaration')
            _, name, module, kind, expression, axioms_raw = parts
            require(name not in declarations, 'duplicate OPICA declaration: '+name)
            require(module in modules, 'foreign defining module')
            # Lean caches constructor congruence lemmas in the current defining
            # module under the original constructor namespace. Enumerate these
            # public helpers with the same type, axiom and dependency audits;
            # the exception never applies to primary root identities.
            generated_congruence = kind == 'THEOREM' and name.endswith('.congr_simp')
            generated_equation = kind == 'THEOREM' and name in generated_equations
            require(name.startswith('Zeta23.OPICARound2.') or generated_congruence or generated_equation,
                'foreign declaration namespace')
            metrics = validate_expression(expression)
            axioms = axioms_raw.split(',') if axioms_raw else []
            require(len(axioms) == len(set(axioms)), 'duplicate axiom')
            require(set(axioms) <= ALLOWED_AXIOMS, 'unadmitted mathematical axiom: '+name)
            require(kind != 'AXIOM', 'new project axiom: '+name)
            declarations[name] = {'name':name, 'module':module, 'kind':kind,
                'type_expression':json.loads(expression), 'type_metrics':metrics,
                'type_sha256':hashlib.sha256(expression.encode()).hexdigest(), 'axioms':axioms}
        elif line.startswith('OPICA2_GENERATED_EQUATION\t'):
            parts = line.split('\t')
            require(len(parts) == 3 and all(parts[1:]), 'malformed generated equation provenance')
            _, name, origin = parts
            require(name not in generated_equations, 'duplicate generated equation provenance')
            generated_equations[name] = origin
        elif line.startswith('OPICA2_CONSTRUCTOR\t'):
            parts = line.split('\t')
            require(len(parts) == 4, 'malformed constructor')
            _, family, name, expression = parts
            require(name not in constructors, 'duplicate constructor: '+name)
            validate_expression(expression)
            constructors[name] = {'family':family, 'type_expression':json.loads(expression)}
        elif line.startswith('OPICA2_PUBLIC_COUNT\t'):
            require(count is None, 'duplicate public count')
            parts = line.split('\t')
            require(len(parts) == 2 and parts[1].isdigit(), 'malformed public count')
            count = int(parts[1])
        elif line.startswith('OPICA2_COMPLETE\t'):
            require(complete is None, 'duplicate terminating completeness record')
            parts = line.split('\t')
            require(len(parts) == 2 and parts[1].isdigit(), 'malformed terminating completeness record')
            complete = int(parts[1])
        elif line.startswith('RHRC_CANDIDATE_RESULT\t'):
            parts = line.split('\t')
            require(len(parts) == 10, 'malformed exact candidate resolution')
            _, identity, status, number, name, module, kind, private, pretty_type, _ = parts
            require(identity not in candidates, 'duplicate root candidate')
            require(status == 'RESOLVED_UNIQUE' and number == '1' and private == '0',
                    'unresolved/private/ambiguous root: '+identity)
            candidates[identity] = {'name':name, 'module':module, 'kind':kind, 'full_type':pretty_type}
        elif line.startswith('RHKG_DEP_DECL\t'):
            parts = line.split('\t')
            require(len(parts) == 5, 'malformed dependency declaration')
            _, name, module, kind, internal = parts
            require(internal in {'0','1'}, 'invalid dependency privacy flag')
            record = (module, kind, internal)
            require(name not in dependency_declarations, 'duplicate dependency declaration')
            dependency_declarations[name] = record
        elif line.startswith('RHKG_DEP_CHANNEL\t'):
            _, name, channel, *targets = line.split('\t')
            require(channel in {'TYPE','VALUE','STRUCTURE'}, 'unknown dependency channel')
            key = (name, channel)
            require(key not in channels, 'duplicate dependency channel')
            require(len(targets) == len(set(targets)) and all(targets), 'invalid dependency targets')
            channels[key] = targets
        elif line.startswith(('OPICA2_', 'RHKG_DEP_', 'RHRC_CANDIDATE_RESULT')):
            raise ValueError('unknown or malformed compiler protocol record')
    require(count is not None and count == len(declarations) and count > 0, 'incomplete public enumeration')
    require(complete == count, 'missing or inconsistent terminating completeness record')
    expected_ids = {root['id'] for root in expected_roots}
    require(set(candidates) == expected_ids, 'missing or extra primary root resolutions')
    for root in expected_roots:
        name = root['full_name']
        require(name in declarations, 'missing root type/axiom export: '+name)
        record = declarations[name]
        candidate = candidates[root['id']]
        require(record['module'] == root['module'] and record['kind'] == root['kind'], 'root module/kind mismatch')
        require(candidate['name'] == name and candidate['module'] == root['module'] and candidate['kind'] == root['kind'],
                'root source resolution mismatch')
        require(bool(candidate['full_type']), 'missing human-readable root type')
        record['full_type'] = candidate['full_type']
        if 'expected_type_sha256' in root:
            require(record['type_sha256'] == root['expected_type_sha256'], 'reviewed expected type changed: '+name)
    validate_generated_equations(generated_equations, declarations, channels, dependency_declarations)
    result = {'declarations':list(declarations.values()), 'constructors':constructors,
        'generated_equations':generated_equations,
        'dependency_declarations':[{'name':name,'module':module,'kind':kind,'internal':internal == '1'}
            for name,(module,kind,internal) in sorted(dependency_declarations.items())],
        'dependencies':[{'source':source,'channel':channel,'targets':targets}
            for (source,channel),targets in sorted(channels.items())]}
    validate_compiler_records(result,expected_roots,mathematical_modules=modules)
    return result


def source_manifest(repo: Path, *, clean: bool = True) -> list[dict[str, Any]]:
    """Hash actual source bytes against immutable Git objects, including modes."""
    if clean:
        require(not contract.git(repo, "status", "--porcelain", "--untracked-files=all"),
                "Compiler receipts require a clean committed checkout")
    result = subprocess.run(["git", "-C", str(repo), "ls-tree", "-r", "-z", "HEAD"],
                            check=True, capture_output=True)
    rows = []
    for entry in result.stdout.split(b"\0"):
        if not entry:
            continue
        metadata, name = entry.split(b"\t", 1)
        mode, kind, oid = metadata.decode("ascii").split()
        require(kind == "blob" and mode in {"100644", "100755"}, "Unsupported source mode or object")
        relative = name.decode("utf-8", errors="strict")
        path = contract.file_at(repo, relative)
        size, blob, digest = contract.actual_blob_identity(path)
        require(blob == oid, "Working source differs from the Git tree: " + relative)
        rows.append({"path": relative, "mode": mode, "git_blob": oid,
                     "bytes": size, "sha256": digest})
    reject_untracked_source_providers(repo, {row["path"] for row in rows})
    return sorted(rows, key=lambda r: r["path"])


def reject_untracked_source_providers(repo: Path, tracked: set[str], *,
                                     verified_package_links: frozenset[str] = frozenset()) -> None:
    """Git status alone misses ignored source files that could shadow imports."""
    require(type(verified_package_links) is frozenset and verified_package_links <= tracked,
            "Package link exceptions must be verified committed paths")
    for directory, names, files in os.walk(repo, followlinks=False):
        base = Path(directory)
        names[:] = [name for name in names if name not in {".git", ".lake"}]
        for name in names:
            require(not (base/name).is_symlink(), "Linked project source directory is not accepted")
        for name in files:
            path = base/name
            relative = path.relative_to(repo).as_posix()
            if path.is_symlink():
                require(relative in verified_package_links,
                        "Unverified linked source file is not accepted: " + relative)
            if path.suffix.lower() not in {".lean", ".py"}:
                continue
            require(relative in tracked and (not path.is_symlink() or relative in verified_package_links),
                    "Ignored/untracked source provider outside the committed census: " + relative)


def package_git_index(payload: bytes) -> dict[str, dict[str, str]]:
    """Read exact package modes and object IDs; a name-only census loses Gitlinks."""
    result = {}
    for entry in payload.split(b"\0"):
        if not entry:
            continue
        metadata, raw_name = entry.split(b"\t", 1)
        mode, kind, blob = metadata.decode("ascii").split()
        name = raw_name.decode("utf-8", errors="strict")
        contract.safe_relative(name)
        require(kind == "blob" and mode in {"100644", "100755", "120000"}
                and re.fullmatch(r"[0-9a-f]{40}", blob) and name not in result,
                "Unsupported or duplicate pinned package Git object: " + name)
        result[name] = {"mode": mode, "git_blob": blob}
    return result


def _package_link_target(source: str, target: str) -> str:
    from pathlib import PurePosixPath, PureWindowsPath
    require(target and not any(ord(c) < 32 for c in target) and "\\" not in target
            and not PurePosixPath(target).is_absolute() and not PureWindowsPath(target).drive,
            "Package Gitlink must have a literal relative in-package target: " + source)
    parts = list(PurePosixPath(source).parent.parts)
    for part in PurePosixPath(target).parts:
        if part in {"", "."}:
            continue
        if part == "..":
            require(bool(parts), "Package Gitlink escapes its package: " + source)
            parts.pop()
        else:
            parts.append(part)
    name = "/".join(parts)
    contract.safe_relative(name)
    return name


def validate_package_symlinks(package: Path, index: Mapping[str, Mapping[str, str]], *,
                              allow_materialized: bool = False, read_blob=None) -> frozenset[str]:
    """Authenticate every committed link and its bounded tracked-file target chain.

    Native symlinks must expose the exact committed readlink bytes. Git's
    core.symlinks=false checkout representation is accepted only when explicitly
    enabled and its regular pointer file is byte-identical to that same blob.
    Neither form admits linked directories, external targets or untracked files.
    """
    root = package.resolve()
    require(type(allow_materialized) is bool, "Materialized-link policy must be Boolean")
    blobs = {}

    def committed(oid):
        require(type(oid) is str and re.fullmatch(r"[0-9a-f]{40}", oid), "Invalid package blob identity")
        if oid not in blobs:
            data = read_blob(oid) if read_blob is not None else subprocess.run(
                ["git", "-C", str(package), "cat-file", "blob", oid],
                check=True, capture_output=True).stdout
            require(type(data) is bytes and hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest() == oid,
                    "Package blob reader returned another committed object")
            blobs[oid] = data
        return blobs[oid]

    def path_without_linked_parents(relative):
        contract.safe_relative(relative)
        path = root / relative
        parent = root
        for component in Path(relative).parts[:-1]:
            parent = parent / component
            require(parent.is_dir() and not parent.is_symlink() and parent.resolve() == parent,
                    "Linked or missing package source directory is not accepted: " + relative)
        return path

    links = {name for name, row in index.items() if row["mode"] == "120000"}
    for first in sorted(links):
        current, visited = first, set()
        for _ in range(33):
            require(current not in visited and current in index,
                    "Cyclic or untracked package Gitlink target: " + current)
            visited.add(current)
            record = index[current]
            path = path_without_linked_parents(current)
            expected = committed(record["git_blob"])
            if record["mode"] == "120000":
                require(len(visited) <= 32, "Package Gitlink chain exceeds 32 links")
                if path.is_symlink():
                    literal = os.readlink(path).encode("utf-8", errors="strict")
                else:
                    require(allow_materialized and path.is_file(),
                            "Missing or unapproved materialized package Gitlink: " + current)
                    literal = path.read_bytes()
                require(literal == expected,
                        "Package Gitlink literal differs from its committed blob: " + current)
                current = _package_link_target(current, expected.decode("utf-8", errors="strict"))
                continue
            require(record["mode"] in {"100644", "100755"} and path.is_file()
                    and not path.is_symlink() and path.resolve() == path,
                    "Package Gitlink must terminate at a committed plain file: " + current)
            actual = path.read_bytes()
            require(actual == expected and hashlib.sha256(actual).digest() == hashlib.sha256(expected).digest(),
                    "Package Gitlink target bytes differ from the committed blob: " + current)
            break
        else:
            require(False, "Package Gitlink chain has no bounded plain-file target")
    return frozenset(links)


def validate_query_plan(plan: Mapping[str, Any]) -> None:
    require(type(plan) is dict and set(plan) == {"mathematical_modules", "validation_modules", "roots"},
            "Exact query plan fields are required; clause acceptance is a separate gate")
    require(type(plan["mathematical_modules"]) is list and type(plan["validation_modules"]) is list,"Module inventories must be lists")
    modules = plan["mathematical_modules"] + plan["validation_modules"]
    require(type(plan["mathematical_modules"]) is list and bool(plan["mathematical_modules"])
            and type(plan["validation_modules"]) is list and len(set(modules)) == len(modules),
            "Missing or duplicate module inventory")
    require(all(type(m) is str and NAME.fullmatch(m) and m.startswith("Zeta23.OPICARound2.") for m in modules),
            "Foreign or executable module name in query plan")
    require(all(".Validation" not in m for m in plan["mathematical_modules"])
            and all(m.startswith("Zeta23.OPICARound2.Validation.") for m in plan["validation_modules"]),
            "Mathematical and validation inventories cross trust boundaries")
    roots = plan["roots"]
    require(type(roots) is list and bool(roots) and all(type(row) is dict
            and type(row.get("id")) is str and type(row.get("full_name")) is str for row in roots),
            "An exact nonempty root query object inventory is required")
    require(len({r.get("id") for r in roots}) == len(roots)
            and len({r.get("full_name") for r in roots}) == len(roots), "Duplicate query identity")
    for row in roots:
        require(type(row) is dict and set(row) <= {"id", "full_name", "module", "kind", "expected_type_sha256"}
                and {"id", "full_name", "module", "kind"} <= set(row), "Malformed exact root query")
        require(all(type(row[k]) is str and NAME.fullmatch(row[k]) for k in ("id", "full_name", "module", "kind")),
                "Executable or malformed query strings")
        require(row["module"] in modules and row["full_name"].startswith("Zeta23.OPICARound2.")
                and row["kind"] in {"THEOREM", "DEFINITION", "INDUCTIVE", "CONSTRUCTOR"},
                "Foreign query module/namespace or wrong kind")
        if "expected_type_sha256" in row:
            require(type(row["expected_type_sha256"]) is str
                    and contract.SHA.fullmatch(row["expected_type_sha256"]), "Invalid independently reviewed type digest")


def render_exporter(repo: Path, plan: Mapping[str, Any]) -> bytes:
    """Only substitute code-free module/query data into frozen audit machinery."""
    validate_query_plan(plan)
    relative = "Zeta23/RHRC/OpicaFollowupBindings.lean"
    original = subprocess.run(["git", "-C", str(repo), "show", contract.FROZEN_COMMIT + ":" + relative],
                              capture_output=True, check=True).stdout
    require(contract.file_at(repo, relative).read_bytes() == original, "Frozen exporter template changed")
    text = original.decode("utf-8").replace("\r\n", "\n")
    text = text.replace("import Zeta23.OPICAFollowup.Validation\n", "")
    text, count = re.subn(r"namespace FollowupDependencyExport\n.*?end FollowupDependencyExport\n",
                          "", text, count=1, flags=re.S)
    require(count == 1, "Frozen dependency-export template boundary changed")
    text = text.replace("FollowupDependencyExport.exportDependencies names", "exportDependencies names")
    text = text.replace("OPICA_FOLLOWUP_", "OPICA2_").replace("Zeta23.OPICAFollowup", "Zeta23.OPICARound2")
    queries = []
    for row in plan["roots"]:
        values = [json.dumps(row[key]) for key in ("id", "module", "full_name", "kind")]
        queries.append("    ({ sourceId := " + values[0] + ", moduleName := " + values[1]
                       + ", shortName := " + values[2] + ", sourceKind := " + values[3]
                       + " } : SourceCandidateQuery)")
    block = "  let queries : Array SourceCandidateQuery := #[\n" + ",\n".join(queries) + "]\n  resolveSourceCandidates queries"
    text, count = re.subn(r"  let queries : Array SourceCandidateQuery := #\[.*?\n  resolveSourceCandidates queries",
                          lambda _: block, text, count=1, flags=re.S)
    require(count == 1, "Frozen query template boundary changed")
    modules = plan["mathematical_modules"] + plan["validation_modules"]
    block = "  let mathematicalModules : Array String := #[\n" + ",\n".join("    " + json.dumps(m) for m in modules) + "]\n  let mut names"
    text, count = re.subn(r"  let mathematicalModules : Array String := #\[.*?\n  let mut names",
                          lambda _: block, text, count=1, flags=re.S)
    require(count == 1, "Frozen module template boundary changed")
    header = "\n".join("import " + m for m in modules) + "\nimport Zeta23.RHRC.DeclarationDependencyExport\n"
    return (header + text).encode("utf-8")


def validate_environment(repo: Path) -> dict[str, str]:
    toolchain = (repo/"lean-toolchain").read_text(encoding="utf-8").strip()
    require(toolchain == "leanprover/lean4:v4.33.0-rc2", "Pinned Lean toolchain changed")
    manifest = load_strict_json(repo/"lake-manifest.json")
    packages = [r for r in manifest["packages"] if r["name"] == "mathlib"]
    require(len(packages) == 1 and packages[0]["rev"] == "51e6992efd06126df61a496bebf8f49482a4e129",
            "Pinned Mathlib revision changed")
    validate_packages(repo)
    return {"lean_toolchain": toolchain, "mathlib_commit": packages[0]["rev"]}


def validate_packages(repo: Path) -> list[dict[str, str]]:
    manifest = load_strict_json(repo/"lake-manifest.json")
    result = []
    seen = set()
    for row in manifest["packages"]:
        name, revision = row.get("name"), row.get("rev")
        require(row.get("type") == "git" and type(name) is str and NAME.fullmatch(name)
                and name not in seen and type(revision) is str and re.fullmatch(r"[0-9a-f]{40}",revision),
                "Every source package needs a unique exact Git revision")
        seen.add(name)
        package = repo/".lake/packages"/name
        require(contract.git(package,"rev-parse","HEAD") == revision
                and not contract.git(package,"status","--porcelain","--untracked-files=all"),
                "Pinned package source is dirty or differs from its commit: " + name)
        tree = subprocess.run(["git", "-C", str(package), "ls-tree", "-r", "-z", "HEAD"],
                              check=True, capture_output=True)
        index = package_git_index(tree.stdout)
        allow_materialized = False
        if any(item["mode"] == "120000" for item in index.values()):
            config = subprocess.run(["git", "-C", str(package), "config", "--bool", "--get", "core.symlinks"],
                                    capture_output=True)
            require(type(config.returncode) is int and config.returncode in {0, 1}
                    and (config.returncode == 1 or config.stdout.strip() in {b"true", b"false"}),
                    "Cannot determine exact pinned package symlink checkout policy: " + name)
            allow_materialized = config.returncode == 0 and config.stdout.strip() == b"false"
        try:
            verified_links = validate_package_symlinks(package, index, allow_materialized=allow_materialized)
            reject_untracked_source_providers(package, set(index), verified_package_links=verified_links)
        except InvalidCertificate as exc:
            raise InvalidCertificate(exc.code, "Pinned package " + name + ": " + str(exc)) from exc
        result.append({"name":name,"commit":revision})
    return sorted(result,key=lambda r:r["name"])


def run_command(repo: Path, argv: list[str], output: Path, name: str, tree: str,
                *, timeout: int = 3600) -> dict[str, Any]:
    """Persist raw stdout/stderr even on failure. Never use a shell or hide exits."""
    require(type(argv) is list and argv and all(type(x) is str and x for x in argv), "Invalid compiler argv")
    require(type(timeout) is int and 1 <= timeout <= 86400, "Compiler timeout must be an exact bounded positive integer")
    stdout_path, stderr_path = output/(name+".stdout.log"), output/(name+".stderr.log")
    require(not stdout_path.exists() and not stderr_path.exists(), "Refuse to overwrite a prior command observation")
    with stdout_path.open("xb") as stdout, stderr_path.open("xb") as stderr:
        process = subprocess.Popen(argv, cwd=repo, stdout=stdout, stderr=stderr)
        try:
            code = process.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            process.kill()
            process.wait()
            raise InvalidCertificate("compiler_timeout", "Compiler command timed out; raw logs preserved")
    return {"argv": argv, "returncode": code, "stdout_sha256": contract.digest(stdout_path),
            "stderr_sha256": contract.digest(stderr_path), "working_tree_sha": tree}


def compiler_commands(plan: Mapping[str, Any], output: Path, lake: str) -> list[tuple[list[str], str]]:
    """Exact compiler recipe, including frozen audit tools and external source root."""
    validate_query_plan(plan)
    modules = plan["mathematical_modules"] + plan["validation_modules"]
    return [([lake, "env", "lean", "--version"], "lean-version"),
            ([lake, "build", *modules, *FACADE_BUILD_TARGETS, *AUDIT_BUILD_TARGETS], "build"),
            ([lake, "env", "lean", "-R", str(output), "-o",
              str(output/"Round2Export.olean"), str(output/"Round2Export.lean")], "bindings")]


def recorded_export_root(commands: list[dict[str, Any]]):
    """Authenticate the producer's absolute path while allowing artifact relocation.

    The recorded path is compared as data. It is never executed or used to read
    supplied files; those are read only below the verifier's artifact directory.
    """
    from pathlib import PurePosixPath, PureWindowsPath
    require(type(commands) is list and len(commands)==3, "Incomplete compiler command inventory")
    argv=commands[2].get("argv")
    require(type(argv) is list and len(argv)==8 and argv[1:4]==["env","lean","-R"]
            and argv[5]=="-o" and all(type(x) is str and x and not any(ord(c)<32 for c in x) for x in argv), "Malformed external exporter command")
    root=PureWindowsPath(argv[4]) if re.match(r"^[A-Za-z]:[\\/]",argv[4]) else PurePosixPath(argv[4])
    require(root.is_absolute() and ".." not in root.parts and argv[6]==str(root/"Round2Export.olean")
            and argv[7]==str(root/"Round2Export.lean"), "External exporter paths do not share one absolute producer root")
    return root


def produce_receipt(repo: Path, output: Path, plan: Mapping[str, Any], *,
                    requested_commit: str | None = None, lake: str = "lake", build_mode: str = "warm",
                    timeout: int = 3600) -> dict[str, Any]:
    """Run the exact plan. Output is intentionally INCOMPLETE until clause review.

    `cold` requires a caller-provided source checkout with no project .lake/build
    directory before execution. Package objects remain explicitly shared/pinned.
    """
    repo, output = repo.resolve(), output.resolve()
    require(not output.is_relative_to(repo), "Compiler artifacts must be outside the source checkout")
    require(not output.exists(), "Use a new evidence directory; prior evidence is immutable")
    validate_query_plan(plan)
    head, tree = contract.git(repo, "rev-parse", "HEAD"), contract.git(repo, "rev-parse", "HEAD^{tree}")
    requested_commit = requested_commit or head
    require(requested_commit == head, "This producer checks an exact PR head, not an implicit merge or projection")
    contract.check_merged_base(repo, load_strict_json(HERE/"ANCESTOR_LOCK.json", 16*1024*1024))
    sources = source_manifest(repo)
    environment = validate_environment(repo)
    require(build_mode in {"warm", "cold"}, "Unknown build isolation mode")
    if build_mode == "cold":
        require(not (repo/".lake/build").exists(), "Cold replay requires no pre-existing project build products")
    output.mkdir(parents=True)
    driver = render_exporter(repo, plan)
    (output/"Round2Export.lean").write_bytes(driver)
    (output/"query-plan.json").write_bytes(json.dumps(plan, ensure_ascii=False, sort_keys=True,
                                                     separators=(",", ":")).encode("utf-8"))
    (output/"source-manifest.json").write_text(json.dumps(sources, indent=2)+"\n", encoding="utf-8")
    commands = []
    def execute(argv, name):
        record = run_command(repo, argv, output, name, tree, timeout=timeout)
        commands.append(record)
        require(record["returncode"] == 0, "Compiler command failed: " + name)
    recipe = compiler_commands(plan, output, lake)
    execute(*recipe[0])
    version = (output/"lean-version.stdout.log").read_text(encoding="utf-8")
    require("version 4.33.0-rc2," in version and "d8b18978322de05a8f3dba51ef03cf5461676c17" in version,
            "Executed Lean binary is not the pinned compiler")
    modules = plan["mathematical_modules"] + plan["validation_modules"]
    execute(*recipe[1])
    execute(*recipe[2])
    parsed = parse_compiler_output((output/"bindings.stdout.log").read_text(encoding="utf-8"),
                                   plan["roots"], mathematical_modules=modules)
    (output/"compiler-records.json").write_text(json.dumps(parsed, ensure_ascii=False, indent=2)+"\n", encoding="utf-8")
    require(source_manifest(repo) == sources and contract.git(repo, "rev-parse", "HEAD") == head,
            "Source checkout changed during compiler execution")
    require(validate_environment(repo) == environment, "Pinned package sources changed during compilation")
    crosswalk = load_strict_json(HERE/"PAPER_CROSSWALK.json", 16*1024*1024)
    clauses = sorted(c["clause_id"] for f in crosswalk["family_bindings"] if f["required_for_full_core"] for c in f["components"])
    receipt = {"schema": "OPICA2_COMPILER_RECEIPT_V1", "requested_commit": requested_commit,
        "checked_commit": head, "checked_tree": tree, "checkout_kind": "PR_HEAD", **environment,
        "source_manifest_sha256": canonical_sha256(sources), "exporter_source_sha256": hashlib.sha256(driver).hexdigest(),
        "exporter_object_sha256": contract.digest(output/"Round2Export.olean"),
        "raw_compiler_log_sha256": contract.digest(output/"bindings.stdout.log"),
        "independent_queries_sha256": canonical_sha256(plan), "commands": commands,
        "root_records_sha256": canonical_sha256(parsed["declarations"]),
        "constructor_records_sha256": canonical_sha256(parsed["constructors"]),
        "dependency_records_sha256": canonical_sha256({k: parsed[k] for k in ("dependency_declarations", "dependencies")}),
        "reparsed_records_match": True, "axioms": sorted({a for d in parsed["declarations"] for a in d["axioms"]}),
        "required_clauses": clauses, "covered_clauses": [], "ancestor_baseline_replay": False,
        "ancestor_current_compatibility": False, "implementation_state": "INCOMPLETE",
        "human_review": "NOT_ESTABLISHED", "review_record_sha256": None,
        "full_release_accepted": False, "RH": "OPEN", "Step4": "OPEN"}
    validate_schema(receipt, load_strict_json(HERE/"schemas/receipt.schema.json"))
    (output/"compiler-receipt.json").write_text(json.dumps(receipt, indent=2)+"\n", encoding="utf-8")
    bundle = {"schema": "OPICA2_COMPILER_BUNDLE_V1", "build_mode": build_mode,
        "project_objects_cold_at_start": build_mode == "cold", "package_objects": "EXISTING_PINNED_CACHE",
        "cold_complete_toolchain_rebuild": False, "fresh_compiler_process": True,
        "pinned_packages": validate_packages(repo),
        "producer_source_sha256": contract.digest(Path(__file__)), "query_plan_sha256": canonical_sha256(plan),
        "files": [{"path": p.name, "sha256": contract.digest(p), "bytes": p.stat().st_size}
                  for p in sorted(output.iterdir()) if p.is_file()],
        "authority": "SOURCE_BOUND_COMPILER_EXPORT_NO_CLAUSE_OR_RELEASE_ACCEPTANCE",
        "full_core_accepted": False, "full_release_accepted": False, "RH": "OPEN", "Step4": "OPEN"}
    (output/"bundle.json").write_text(json.dumps(bundle, indent=2)+"\n", encoding="utf-8")
    return receipt


def verify_receipt_artifacts(receipt: Mapping[str, Any], repo: Path, artifacts: Path,
                            plan: Mapping[str, Any]) -> dict[str, Any]:
    """Independent raw-log reparse and source/object/command checks, not fresh replay."""
    validate_schema(receipt, load_strict_json(HERE/"schemas/receipt.schema.json"))
    require(receipt["implementation_state"] == "INCOMPLETE" and receipt["covered_clauses"] == []
            and receipt["ancestor_baseline_replay"] is False and receipt["ancestor_current_compatibility"] is False
            and receipt["human_review"] == "NOT_ESTABLISHED" and receipt["review_record_sha256"] is None
            and receipt["full_release_accepted"] is False,
            "Scoped producer evidence cannot be promoted by flipping acceptance/coverage fields")
    validate_query_plan(plan)
    artifacts = artifacts.resolve()
    require(receipt["checked_commit"] == contract.git(repo, "rev-parse", "HEAD")
            and receipt["checked_tree"] == contract.git(repo, "rev-parse", "HEAD^{tree}"), "Stale receipt source")
    require(receipt["source_manifest_sha256"] == canonical_sha256(source_manifest(repo)), "Changed source manifest")
    require(receipt["independent_queries_sha256"] == canonical_sha256(plan), "Substituted query plan")
    driver = render_exporter(repo, plan)
    require((artifacts/"Round2Export.lean").read_bytes() == driver
            and receipt["exporter_source_sha256"] == hashlib.sha256(driver).hexdigest()
            and receipt["exporter_object_sha256"] == contract.digest(artifacts/"Round2Export.olean"), "Exporter identity differs")
    require(len(receipt["commands"]) == 3, "Incomplete compiler command inventory")
    producer_root = recorded_export_root(receipt["commands"])
    expected = compiler_commands(plan, producer_root, receipt["commands"][0]["argv"][0])
    for row, (argv, name) in zip(receipt["commands"], expected):
        require(row["argv"] == argv and type(row["returncode"]) is int and row["returncode"] == 0
                and row["working_tree_sha"] == receipt["checked_tree"], "Compiler command failed or changed")
        for channel in ("stdout", "stderr"):
            require(contract.digest(artifacts/(name+"."+channel+".log")) == row[channel+"_sha256"], "Raw command log changed")
    require(receipt["raw_compiler_log_sha256"] == contract.digest(artifacts/"bindings.stdout.log"), "Raw exporter log changed")
    modules = plan["mathematical_modules"] + plan["validation_modules"]
    parsed = parse_compiler_output((artifacts/"bindings.stdout.log").read_text(encoding="utf-8"),
                                   plan["roots"], mathematical_modules=modules)
    saved = load_strict_json(artifacts/"compiler-records.json", 64*1024*1024)
    require(saved == parsed, "Serialized compiler records differ from the independent raw-log parse")
    require(receipt["root_records_sha256"] == canonical_sha256(parsed["declarations"])
            and receipt["constructor_records_sha256"] == canonical_sha256(parsed["constructors"])
            and receipt["dependency_records_sha256"] == canonical_sha256({k: parsed[k] for k in ("dependency_declarations", "dependencies")})
            and receipt["axioms"] == sorted({a for d in parsed["declarations"] for a in d["axioms"]}),
            "Receipt hashes or axioms differ from compiler evidence")
    environment = validate_environment(repo)
    require(all(receipt[k] == v for k, v in environment.items()), "Receipt package/toolchain differs")
    version = (artifacts/"lean-version.stdout.log").read_text(encoding="utf-8")
    require("version 4.33.0-rc2," in version and "d8b18978322de05a8f3dba51ef03cf5461676c17" in version, "Wrong compiler version log")
    return {"status": "PASS_SOURCE_OBJECT_AND_RAW_LOG_REPARSE_ONLY", "fresh_compiler_replay": False,
            "declarations": len(parsed["declarations"]), "parsed": parsed,
            "full_core_accepted": False, "full_release_accepted": False, "RH": "OPEN", "Step4": "OPEN"}



# Full-core composition is independent of the intentionally narrow raw receipt.
# Source declarations below are navigation/hash bindings; only compiler DAGs
# establish their complete elaborated types and project dependency closure.
SEMANTIC_FIELDS = ("clause_id","family_id","normative_component_scope","primary_declaration",
    "literal_consumer_statements","load_bearing_declarations","negative_control_declarations",
    "consumer_dependency_bindings","source_binding","control_ids","scoped_control_bindings_sha256",
    "reviewed_control_applicability")


def compiler_plan_data(plan: Mapping[str, Any]) -> dict:
    if type(plan) is dict and plan.get("schema")=="OPICA2_SEMANTIC_QUERY_PLAN_V1":
        require(set(plan)=={"schema","compiler_plan","declaration_bindings","component_implementation_bindings","scoped_control_bindings"},
                "Unexpected semantic query packet fields")
        plan=plan["compiler_plan"]
    validate_query_plan(plan)
    return dict(plan)


def masked_lean_source(text: str) -> str:
    """Mask comments/strings with spaces while preserving every offset and line."""
    out=list(text);i=0;depth=0
    def blank(start,stop):
        for index in range(start,stop):
            if text[index]!="\n":out[index]=" "
    while i<len(text):
        if depth:
            if text.startswith("/-",i):blank(i,i+2);depth+=1;i+=2
            elif text.startswith("-/",i):blank(i,i+2);depth-=1;i+=2
            else:blank(i,i+1);i+=1
        elif text.startswith("/-",i):blank(i,i+2);depth=1;i+=2
        elif text.startswith("--",i):
            end=text.find("\n",i);end=len(text) if end<0 else end
            blank(i,end);i=end
        elif text.startswith('s!"',i):
            require(False,"Interpolated source literals need an explicit reviewed locator parser")
        elif text[i]=='r' and (i==0 or not (text[i-1].isalnum() or text[i-1]=='_')) and re.match(r'r#*"',text[i:]):
            # Raw Lean strings use r###"..."###; hashes are literal delimiters.
            prefix=re.match(r'r#*"',text[i:]).group(0)
            hashes=prefix[1:-1];end=text.find('"'+hashes,i+len(prefix))
            require(end>=0,"Unterminated raw Lean source literal")
            stop=end+1+len(hashes);blank(i,stop);i=stop
        elif text[i]=='"':
            start=i;i+=1;closed=False
            while i<len(text):
                if text[i]=='\\':i=min(len(text),i+2)
                elif text[i]=='"':i+=1;closed=True;break
                else:i+=1
            require(closed,"Unterminated Lean source literal");blank(start,i)
        else:i+=1
    require(depth==0,"Unterminated Lean source comment")
    return "".join(out)


def source_declarations(path: Path) -> dict[str, dict]:
    """Reproduce the reviewed source locators without treating them as kernel types."""
    text=path.read_text(encoding="utf-8").replace("\r\n","\n")
    stack=[]; found=[]; offset=0
    pattern=re.compile(r"^\s*(?:(private|protected|noncomputable) )?(theorem|lemma|def|abbrev|structure)\s+([\w\u0080-\uffff.]+)")
    for line_number,(original,line) in enumerate(zip(text.splitlines(True),masked_lean_source(text).splitlines(True)),1):
        ns=re.match(r"^\s*namespace\s+(\S+)",line)
        section=re.match(r"^\s*(?:noncomputable )?section(?:\s+\S+)?\s*$",line.rstrip())
        end=re.match(r"^\s*end(?:\s+\S+)?\s*$",line.rstrip())
        if ns: stack.append(("namespace",ns.group(1)))
        elif section: stack.append(("section",""))
        elif end and stack: stack.pop()
        match=pattern.match(line)
        if match:
            prefix=".".join(value for kind,value in stack if kind=="namespace")
            name=(prefix+"." if prefix else "")+match.group(3)
            found.append({"full_name":name,"line":line_number,"offset":offset,"private":match.group(1)=="private"})
        offset+=len(original)
    result={}
    for index,row in enumerate(found):
        stop=found[index+1]["offset"] if index+1<len(found) else len(text)
        body=text[row["offset"]:stop]
        if not row["private"]:
            require(row["full_name"] not in result,"Duplicate lexical declaration binding")
            result[row["full_name"]]={"line":row["line"],"body":body,"header":body.split(":=",1)[0],
                "literal_statement_sha256":hashlib.sha256(body.split(":=",1)[0].encode("utf-8")).hexdigest(),
                "source_declaration_sha256":hashlib.sha256(body.encode("utf-8")).hexdigest()}
    return result


def dependency_reachable(parsed: Mapping[str,Any], name: str, *, value_only: bool=False) -> set[str]:
    channels={}
    for row in parsed["dependencies"]:
        if not value_only or row["channel"]=="VALUE":
            channels.setdefault(row["source"],set()).update(row["targets"])
    reached=set(); pending=list(channels.get(name,()))
    while pending:
        node=pending.pop()
        if node in reached: continue
        reached.add(node);pending.extend(channels.get(node,()))
    return reached


def _indexed_bindings(rows, field):
    require(type(rows) is list and all(type(row) is dict and type(row.get(field)) is str for row in rows),
            "Malformed exact implementation binding inventory")
    result={row[field]:row for row in rows}
    require(len(result)==len(rows),"Duplicate implementation binding identity")
    return result


def verify_component_bindings(repo: Path, parsed: Mapping[str,Any], plan: Mapping[str,Any],
                              crosswalk: Mapping[str,Any], control_dispositions: Mapping[str,dict],
                              *, public: Mapping[str,Any]) -> dict:
    """Derive clause coverage from exact source, full compiler types and proof VALUE edges."""
    try:
        from . import controls
    except ImportError:
        import controls
    compiler_plan=compiler_plan_data(plan)
    modules=compiler_plan["mathematical_modules"]+compiler_plan["validation_modules"]
    validate_compiler_records(parsed,compiler_plan["roots"],mathematical_modules=modules)
    controls.check_control_bindings(contract.control_mapping(repo/"research/RHRC/integration/opica_round2",crosswalk))
    components=_indexed_bindings(crosswalk["component_implementation_bindings"],"clause_id")
    scoped_controls=_indexed_bindings(crosswalk["scoped_control_bindings"],"control_id")
    roots={row["id"]:row for row in public["roots"]}
    declarations={row["name"]:row for row in parsed["declarations"]}
    normative={c["clause_id"]:(family,c) for family in crosswalk["family_bindings"] for c in family["components"]}
    require(set(components)==set(normative) and len(components)==143,"Incomplete 143-clause disposition inventory")
    require(set(scoped_controls)==set(control_dispositions) and len(scoped_controls)==75,"Incomplete 75-control disposition inventory")
    if type(plan) is dict and plan.get("schema")=="OPICA2_SEMANTIC_QUERY_PLAN_V1":
        require(canonical_sha256(plan["component_implementation_bindings"])==canonical_sha256(components)
                and canonical_sha256(plan["scoped_control_bindings"])==canonical_sha256(scoped_controls),
                "External semantic packet differs from the committed clause/control bindings")
    locations={}; source_hashes={}
    def located(name):
        require(name in declarations,"A bound declaration is absent from the full compiler export: "+name)
        record=declarations[name]
        path=record["module"].replace(".","/")+".lean"
        if path not in locations:
            file=contract.file_at(repo,path)
            require(file.is_file(),"Bound compiler module source is absent")
            locations[path]=source_declarations(file);source_hashes[path]=contract.digest(file)
        require(name in locations[path],"A compiler declaration lacks its reviewed literal source declaration: "+name)
        return record,path,locations[path][name]
    if type(plan) is dict and plan.get("schema")=="OPICA2_SEMANTIC_QUERY_PLAN_V1":
        rows=_indexed_bindings(plan["declaration_bindings"],"full_name")
        require(set(rows)=={row["full_name"] for row in compiler_plan["roots"]},"Semantic source bindings differ from exact query population")
        for name,row in rows.items():
            record,path,location=located(name)
            require(row["source_path"]==path and row["source_sha256"]==source_hashes[path]
                    and row["line"]==location["line"] and row["literal_statement_sha256"]==location["literal_statement_sha256"]
                    and row["source_declaration_sha256"]==location["source_declaration_sha256"],"Semantic declaration source/hash mismatch: "+name)
    covered=[]; disabled=[]; evidence=[]
    for clause_id,(family,clause) in normative.items():
        row=components[clause_id]
        require(row["family_id"]==family["family_id"],"Clause crossed family identity")
        if not family["required_for_full_core"]:
            require(row.get("status")=="OPTIONAL_DISABLED" and row.get("acceptance") is False
                    and not row.get("primary_declaration"),"Optional clause was silently activated")
            disabled.append(clause_id);continue
        require(row.get("normative_component_scope")==clause["statement_or_scope"],"Clause normative scope changed")
        control_ids=[link["control_id"] for link in clause["controls"]]
        require(row["control_ids"]==control_ids,"Clause control selection changed")
        require(row["scoped_control_bindings_sha256"]==canonical_sha256([scoped_controls[k] for k in control_ids]),
                "Clause did not bind its complete ordered control records")
        require(row["semantic_binding_sha256"]==canonical_sha256({k:row[k] for k in SEMANTIC_FIELDS}),
                "Clause semantic binding digest differs")
        family_root=roots.get(family["family_id"])
        require(family_root is not None and family_root.get("required_for_full_core") is True,
                "Required family primary root absent")
        primary=row["primary_declaration"]
        require(primary==family_root["proposed_public_name"]==family_root.get("actual_public_declaration"),
                "Clause bound a substitute primary declaration")
        primary_record,primary_path,_=located(primary)
        require(primary_record["kind"]=="THEOREM" and primary_record["module"]==family_root["module"],
                "Primary declaration has wrong compiler kind/module")
        source=row["source_binding"]
        require(source["path"]==primary_path and source["module"]==primary_record["module"]
                and source["sha256"]==source_hashes[primary_path],"Primary source binding is stale")
        expected=row["expected_type_consumers"];domain=row["actual_domain_consumers"]
        require(type(expected) is list and expected and len(set(expected))==len(expected)
                and type(domain) is list and domain and set(domain)<=set(expected),"Missing independent expected-type/native-domain consumers")
        dependencies=_indexed_bindings(row["consumer_dependency_bindings"],"declaration")
        literals=_indexed_bindings(row["literal_consumer_statements"],"declaration")
        require(set(expected)==set(dependencies)==set(literals),"Consumer expected types and dependency bindings differ")
        consumer_records=[]; load_bearing=False
        for name in expected:
            record,path,location=located(name)
            require(record["kind"]=="THEOREM" and record["module"] in compiler_plan["validation_modules"]
                    and record["module"]!=primary_record["module"] and name!=primary,
                    "Expected-type consumer crossed the independent Validation boundary")
            require(path==source["validation_path"] and source["validation_sha256"]==source_hashes[path],"Validation source pin is stale")
            for binding in (dependencies[name],literals[name]):
                require(binding["path"]==path and binding["line"]==location["line"]
                        and binding["literal_statement_sha256"]==location["literal_statement_sha256"],
                        "Literal expected-type binding changed: "+name)
            require(":=" in location["body"] and primary not in location["header"],
                    "A primary signature alias cannot replace a literal expected-type consumer")
            required=dependencies[name]["required_load_bearing_declarations"]
            require(type(required) is list and len(set(required))==len(required),"Malformed consumer proof requirements")
            reach=dependency_reachable(parsed,name,value_only=True)
            require(set(required)<=reach,"Consumer proof does not use its required mathematical declarations through VALUE edges: "+name)
            load_bearing=load_bearing or bool(required)
            consumer_records.append({"name":name,"type_sha256":record["type_sha256"],"axioms":record["axioms"],
                                     "literal_statement_sha256":location["literal_statement_sha256"],
                                     "required_value_dependencies":required})
        require(load_bearing,"Clause has only source aliases/reflexive navigation consumers")
        for name in row["load_bearing_declarations"]+row["negative_control_declarations"]:
            located(name)
        control_records=[]
        for link in clause["controls"]:
            control=control_dispositions[link["control_id"]]
            require(control.get("verified") is True and set(control["evidence_classes"]) & set(link["accepted_evidence_classes"]),
                    "Clause control lacks its permitted independently verified evidence class: "+clause_id+":"+link["control_id"])
            if link["control_id"]=="OPICA2_G10":
                review=row.get("reviewed_control_applicability",{}).get("OPICA2_G10")
                require(review is not None and review in scoped_controls["OPICA2_G10"].get("required_core_clause_reviews",[])
                        and review["clause_id"]==clause_id and review["primary_declaration"]==primary,
                        "Activated core clause lacks exact optional-activation firewall review")
                actual=[];pending=[primary_record["module"]];seen=set()
                while pending:
                    module=pending.pop()
                    if module in seen:continue
                    seen.add(module);path=module.replace(".","/")+".lean"
                    file=contract.file_at(repo,path)
                    require(file.is_file(),"Reviewed import-closure source is absent")
                    actual.append({"module":module,"source_path":path,"source_sha256":contract.digest(file)})
                    pending.extend(x for x in contract.imports(file.read_text(encoding="utf-8")) if x.startswith("Zeta23.OPICARound2."))
                require(sorted(actual,key=lambda x:x["module"])==review["round2_source_import_closure"]
                        and not set(review["excluded_optional_modules"])&seen,"Optional activation firewall source/import closure differs")
            control_records.append({"control_id":link["control_id"],"disposition_sha256":canonical_sha256(control)})
        covered.append(clause_id)
        evidence.append({"clause_id":clause_id,"family_id":family["family_id"],"primary_declaration":primary,
                         "primary_type_sha256":primary_record["type_sha256"],"semantic_binding_sha256":row["semantic_binding_sha256"],
                         "consumers":consumer_records,"controls":control_records})
    require(len(covered)==125 and len(disabled)==18,"Exact required/disabled clause population changed")
    return {"status":"PASS_COMPILER_SOURCE_AND_CLAUSE_BINDINGS","covered_clauses":sorted(covered),
            "disabled_optional_clauses":sorted(disabled),"clause_records":evidence,
            "required_families":40,"required_clauses":125,"total_dispositions":143,
            "independent_human_review":"NOT_ESTABLISHED","full_release_accepted":False,"RH":"OPEN","Step4":"OPEN"}



def verify_ancestry_bundle(repo: Path, report_path: Path) -> dict:
    """Reconstruct both frozen baselines and both current compatibility exports."""
    try:
        from . import dependency_delta as delta
    except ImportError:
        import dependency_delta as delta
    data=load_strict_json(report_path,32*1024*1024)
    fixed={"schema":"OPICA2_AUTHENTICATED_ANCESTRY_RUN_V1","status":"PASS_EXECUTED_BASELINE_AND_CURRENT_COMPILER_COMPARISON",
        "fresh_processes_executed_here":True,"provider_authenticity_established_here":False,
        "ancestor_baseline_replay":True,"ancestor_current_compatibility":True,
        "scope":"FROZEN_76_100_BASELINES_AND_CURRENT_SOURCE_BOUND_COMPILER_COMPATIBILITY",
        "full_core_accepted":False,"full_release_accepted":False,"human_review":"NOT_ESTABLISHED","RH":"OPEN","Step4":"OPEN"}
    require(type(data) is dict and set(data)==set(fixed)|{"checked_commit","checked_tree","inputs","comparison","source_manifest_sha256"}
            and all(type(data.get(k)) is type(v) and data[k]==v for k,v in fixed.items()),
            "Ancestry execution envelope or authority caps changed")
    require(data.get("source_manifest_sha256")==canonical_sha256(source_manifest(repo)),"Ancestry execution source census changed")
    require(data.get("schema")=="OPICA2_AUTHENTICATED_ANCESTRY_RUN_V1","End-to-end ancestry evidence is required")
    head,tree=contract.git(repo,"rev-parse","HEAD"),contract.git(repo,"rev-parse","HEAD^{tree}")
    require(data.get("checked_commit")==head and data.get("checked_tree")==tree,"Ancestry evidence mixes source heads")
    inputs=data.get("inputs")
    require(type(inputs) is list and len(inputs)==4 and all(type(row) is dict for row in inputs) and {row.get("role") for row in inputs}=={"baseline76","current76","baseline100","current100"},
            "Both frozen and current76/100 source/compiler artifacts are mandatory")
    by_role={row["role"]:row for row in inputs}
    exports=[]
    for role,population,commit,source_tree in (("baseline76",76,contract.FROZEN_COMMIT,contract.FROZEN_TREE),
        ("current76",76,head,tree),("baseline100",100,contract.FROZEN_COMMIT,contract.FROZEN_TREE),("current100",100,head,tree)):
        row=by_role[role]
        require(type(row) is dict and set(row)=={"role","receipt","receipt_sha256"},"Unexpected ancestry input fields")
        path=contract.file_at(report_path.parent,contract.safe_relative(row["receipt"]))
        require(contract.digest(path)==row.get("receipt_sha256"),"Ancestry input receipt changed")
        verify=delta.verify_legacy if role.startswith("baseline") else delta.verify_current_export
        exports.append(verify(repo,path,path.parent,population=population,expected_commit=commit,expected_tree=source_tree))
    comparison=delta.ancestry_report(*exports,current_commit=head,current_tree=tree)
    require(canonical_sha256(data.get("comparison"))==canonical_sha256(comparison),"Stored ancestry equality differs from independent compiler reparse")
    # These flags concern source-bound raw compiler evidence, not the freshness
    # or identity of a remote provider. The nested historical comparator remains
    # unchanged and explicitly reports that a reparse is not a fresh execution.
    return {"status":"PASS_SOURCE_BOUND_BASELINE_AND_CURRENT_COMPATIBILITY","checked_commit":head,"checked_tree":tree,
            "baseline_raw_artifacts_verified":True,"current_raw_artifacts_verified":True,
            "comparison":comparison,"upstream_parsed":exports[3]["parsed"],
            "report_sha256":contract.digest(report_path),"fresh_compiler_replay":False,
            "provider_authenticity_established_here":False,"full_release_accepted":False,"RH":"OPEN","Step4":"OPEN"}


def verify_compiler_bundle(repo: Path, artifacts: Path, receipt: Mapping[str,Any], plan: Mapping[str,Any]) -> dict:
    bundle=load_strict_json(artifacts/"bundle.json",16*1024*1024)
    fixed={"schema":"OPICA2_COMPILER_BUNDLE_V1","package_objects":"EXISTING_PINNED_CACHE",
           "cold_complete_toolchain_rebuild":False,"fresh_compiler_process":True,
           "authority":"SOURCE_BOUND_COMPILER_EXPORT_NO_CLAUSE_OR_RELEASE_ACCEPTANCE",
           "full_core_accepted":False,"full_release_accepted":False,"RH":"OPEN","Step4":"OPEN"}
    require(type(bundle) is dict and set(bundle)==set(fixed)|{"build_mode","project_objects_cold_at_start","pinned_packages",
            "producer_source_sha256","query_plan_sha256","files"}
            and all(type(bundle.get(k)) is type(v) and bundle[k]==v for k,v in fixed.items()),
            "Compiler bundle contains unknown fields or altered authority caps")
    require(bundle.get("schema")=="OPICA2_COMPILER_BUNDLE_V1" and bundle.get("build_mode")=="cold"
            and bundle.get("project_objects_cold_at_start") is True and bundle.get("cold_complete_toolchain_rebuild") is False
            and bundle.get("package_objects")=="EXISTING_PINNED_CACHE", "Required aggregate must record a cold project build with explicit pinned package cache scope")
    require(bundle.get("producer_source_sha256")==contract.digest(Path(__file__))
            and bundle.get("query_plan_sha256")==canonical_sha256(plan)
            and bundle.get("pinned_packages")==validate_packages(repo),"Compiler bundle source, query plan or package pins differ")
    expected={"Round2Export.lean","Round2Export.olean","query-plan.json","source-manifest.json","compiler-records.json","compiler-receipt.json"}
    expected|={name+"."+channel+".log" for name in ("lean-version","build","bindings") for channel in ("stdout","stderr")}
    rows=bundle.get("files")
    require(type(rows) is list and len(rows)==len(expected) and all(type(row) is dict for row in rows) and {row.get("path") for row in rows}==expected,"Incomplete compiler bundle artifact inventory")
    for row in rows:
        path=contract.file_at(artifacts,row["path"])
        require(type(row) is dict and set(row)=={"path","sha256","bytes"} and type(row.get("bytes")) is int
                and row.get("sha256")==contract.digest(path) and row["bytes"]==path.stat().st_size,"Compiler bundle artifact changed")
    require(canonical_sha256(load_strict_json(artifacts/"compiler-receipt.json",32*1024*1024))==canonical_sha256(receipt)
            and canonical_sha256(load_strict_json(artifacts/"query-plan.json",32*1024*1024))==canonical_sha256(plan),"Bundle raw receipt/query plan differs")
    return {"build_scope":"RECORDED_COLD_PROJECT_START_PINNED_PACKAGE_OBJECTS_ALLOWED",
            "bundle_sha256":contract.digest(artifacts/"bundle.json"),"provider_authenticity_established_here":False}


def _registered_dependency_report(claims: Mapping[str,Any], bindings: Mapping[str,Any],
                                  public: Mapping[str,Any], old_claims: Mapping[str,Any],
                                  old_bindings: Mapping[str,Any], parsed: Mapping[str,Any], mapper) -> dict:
    """Pure exact-use comparison; caller supplies independently verified compiler data."""
    by_claim=_indexed_bindings(claims["claims"],"id")
    by_binding=_indexed_bindings(bindings["bindings"],"id")
    old_claim_by_id=_indexed_bindings(old_claims["claims"],"id")
    old_binding_by_id=_indexed_bindings(old_bindings["bindings"],"id")
    require(len(old_claim_by_id)==298 and len(old_binding_by_id)==294,
            "Frozen registered claim/binding population changed")
    roots=[row for row in public["roots"] if row["required_for_full_core"]]
    require(len(roots)==40 and {row["id"] for row in roots}==contract.MANDATORY,
            "Required public registered root identities differ from the exact forty")
    require(len(by_claim)==338 and set(by_claim)==set(old_claim_by_id)|contract.MANDATORY
            and len(by_binding)==334 and set(by_binding)==set(old_binding_by_id)|contract.MANDATORY,
            "Registered population is not the frozen parent plus exactly forty required claims")
    require(len({row["theorem"] for row in by_binding.values()})==334,
            "Registered theorem names are not distinct")
    for identity,record in old_claim_by_id.items():
        require(canonical_sha256(by_claim[identity])==canonical_sha256(record),
                "Original registered claim object changed: "+identity)
    for identity,record in old_binding_by_id.items():
        require(canonical_sha256(by_binding[identity])==canonical_sha256(record),
                "Original registered theorem binding changed: "+identity)
    require(canonical_sha256(bindings.get("candidate_bindings",[]))
            ==canonical_sha256(old_bindings.get("candidate_bindings",[])),
            "Original candidate binding objects changed")
    declarations={row["name"]:row for row in parsed["declarations"]}
    for root in roots:
        identity,name=root["id"],root["proposed_public_name"]
        claim,binding=by_claim[identity],by_binding[identity]
        require(claim["theorem"]==binding["theorem"]==name
                and claim["source"]==binding["source"]==root["module"].replace(".","/")+".lean"
                and claim["status"]==claim["promotion_cap"]=="PROVED_UNCONDITIONAL",
                "New registered source/name/status identity changed: "+identity)
        require(name in declarations and declarations[name]["module"]==root["module"]
                and declarations[name]["kind"]=="THEOREM",
                "Actual compiler declaration is absent or differs from the registered root: "+identity)
    mapped=mapper([row["proposed_public_name"] for row in roots],bindings["bindings"],parsed["dependencies"])
    rows=[]
    for root in sorted(roots,key=lambda row:row["id"]):
        identity,name=root["id"],root["proposed_public_name"]
        actual=by_claim[identity].get("dependencies")
        require(type(actual) is list and all(type(value) is str for value in actual)
                and actual==sorted(set(actual)) and actual==mapped[name],
                "New registered dependencies differ from exact transitive TYPE/VALUE/STRUCTURE compiler uses: "+identity)
        rows.append({"claim_id":identity,"theorem":name,"dependencies":mapped[name],
                     "compiler_type_sha256":declarations[name]["type_sha256"]})
    return {"schema":"OPICA2_NEW_REGISTERED_DEPENDENCIES_V1",
            "status":"PASS_EXACT_FORTY_REGISTERED_COMPILER_USES","rows":rows,
            "registered_binding_universe":334,"preserved_original_claims":298,
            "preserved_original_proved_bindings":294,"compared_new_claims":40,
            "mapping_sha256":canonical_sha256(rows),
            "rule":"EXACT_TRANSITIVE_TYPE_VALUE_STRUCTURE_REGISTERED_CONSTANT_USES",
            "interpretation":"Directed compiler-use provenance through private helpers; not mathematical necessity or independence.",
            "fresh_compiler_replay":False,"provider_authenticity_established_here":False,
            "full_core_accepted":False,"full_release_accepted":False,"RH":"OPEN","Step4":"OPEN"}


def verify_registered_claim_dependencies(repo: Path, parsed: Mapping[str,Any]) -> dict:
    """Bind the exact new forty claim edges without invoking a frozen release CLI."""
    claim_path="research/RHRC/CLAIM_REGISTRY.json"
    binding_path="research/RHRC/REGISTERED_THEOREM_BINDINGS.json"
    public_path="research/RHRC/integration/opica_round2/PUBLIC_ROOTS.json"
    def old(path):
        payload=subprocess.run(["git","-C",str(repo),"show",contract.FROZEN_COMMIT+":"+path],
                               capture_output=True,check=True).stdout
        return loads_strict_json(payload,16*1024*1024)
    claims=load_strict_json(contract.file_at(repo,claim_path),16*1024*1024)
    bindings=load_strict_json(contract.file_at(repo,binding_path),16*1024*1024)
    public=load_strict_json(contract.file_at(repo,public_path),16*1024*1024)
    parent=frozen_tool(repo,"research/RHRC/integration/opica/build_receipt.py",
                       "_opica2_frozen_registered_use_mapper")
    report=_registered_dependency_report(claims,bindings,public,old(claim_path),old(binding_path),
                                         parsed,parent.mapped_registered_dependencies)
    report["source_files"]=[{"path":path,"sha256":contract.digest(contract.file_at(repo,path))}
                            for path in (claim_path,binding_path,public_path)]
    report["frozen_ancestor"]=contract.FROZEN_COMMIT
    return report


def compose_core_evidence(repo: Path, raw_receipt_path: Path, artifacts: Path, plan: Mapping[str,Any], *,
                          clause_evidence: Path, control_evidence: Path,
                          optimized_control_evidence: Path, ancestry_evidence: Path) -> dict:
    """Derive a separate full-core compiler receipt without promoting raw JSON fields."""
    from copy import deepcopy
    try:
        from . import controls
    except ImportError:
        import controls
    here=repo/"research/RHRC/integration/opica_round2"
    compiler_plan=compiler_plan_data(plan)
    workflow=load_strict_json(here/"WORKFLOW_CONTRACT.json",16*1024*1024)
    require(compiler_plan==workflow["compiler_query_plan"]
            and canonical_sha256(compiler_plan)==workflow["compiler_query_plan_sha256"],
            "Full-core composition requires the independently reviewed committed exact query inventory")
    raw=load_strict_json(raw_receipt_path,32*1024*1024)
    verified=verify_receipt_artifacts(raw,repo,artifacts,compiler_plan)
    isolation=verify_compiler_bundle(repo,artifacts,raw,compiler_plan)
    registered_dependencies=verify_registered_claim_dependencies(repo,verified["parsed"])
    canonical=load_strict_json(here/"PAPER_CROSSWALK.json",16*1024*1024)
    require(canonical_sha256(load_strict_json(clause_evidence,16*1024*1024))==canonical_sha256(canonical),"Supplied clause evidence differs from the committed complete crosswalk")
    bindings=_indexed_bindings(canonical["scoped_control_bindings"],"control_id")
    normal=controls.verify_runtime_control_evidence(repo,control_evidence,bindings,optimized=False)
    optimized=controls.verify_runtime_control_evidence(repo,optimized_control_evidence,bindings,optimized=True)
    ancestry=verify_ancestry_bundle(repo,ancestry_evidence)
    dispositions=controls.compose_control_dispositions(repo,canonical,verified["parsed"],normal=normal,
        optimized=optimized,upstream_parsed=ancestry["upstream_parsed"])
    coverage=verify_component_bindings(repo,verified["parsed"],plan,canonical,dispositions,
                                      public=load_strict_json(here/"PUBLIC_ROOTS.json",16*1024*1024))
    require(raw["required_clauses"]==coverage["covered_clauses"],"Producer required clauses differ from independently derived coverage")
    require(contract.git(repo,"rev-parse","HEAD")==raw["checked_commit"]
            and contract.git(repo,"rev-parse","HEAD^{tree}")==raw["checked_tree"]
            and canonical_sha256(source_manifest(repo))==raw["source_manifest_sha256"],
            "Source changed while compiler, ancestry, controls and clauses were composed")
    composed=deepcopy(raw)
    composed.update({"implementation_state":"FULL_CORE_COMPILER_VERIFIED","covered_clauses":coverage["covered_clauses"],
                     "ancestor_baseline_replay":True,"ancestor_current_compatibility":True})
    validate_schema(composed,load_strict_json(here/"schemas/receipt.schema.json"))
    return {"schema":"OPICA2_CORE_COMPOSITION_V1","status":"PASS_FULL_CORE_COMPILER_COMPOSITION_HUMAN_REVIEW_PENDING",
            "checked_commit":raw["checked_commit"],"checked_tree":raw["checked_tree"],
            "raw_receipt_sha256":contract.digest(raw_receipt_path),"raw_receipt_remains_incomplete":True,
            "query_plan_sha256":canonical_sha256(plan),"clause_evidence_sha256":contract.digest(clause_evidence),
            "normal_control_evidence_sha256":contract.digest(control_evidence),
            "optimized_control_evidence_sha256":contract.digest(optimized_control_evidence),
            "ancestry_evidence_sha256":contract.digest(ancestry_evidence),"isolation":isolation,
            "registered_claim_dependencies":registered_dependencies,
            "coverage":coverage,"control_dispositions":dispositions,
            "ancestry":{"status":ancestry["status"],"report_sha256":ancestry["report_sha256"],
                        "fresh_compiler_replay":False,"provider_authenticity_established_here":False},
            "composed_receipt":composed,"implementation_state":"FULL_CORE_COMPILER_VERIFIED",
            "human_review":"NOT_ESTABLISHED","full_core_compiler_verified":True,
            "full_core_accepted":False,"full_release_accepted":False,"RH":"OPEN","Step4":"OPEN"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=REPO)
    parser.add_argument("--query-plan", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--requested-commit")
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--build-mode", choices=("warm", "cold"), default="warm")
    parser.add_argument("--timeout", type=int, default=3600)
    args = parser.parse_args()
    output_existed = args.output_dir.exists()
    try:
        receipt = produce_receipt(args.repo, args.output_dir, load_strict_json(args.query_plan),
            requested_commit=args.requested_commit, lake=args.lake, build_mode=args.build_mode, timeout=args.timeout)
        print(json.dumps({"status": "PASS_SCOPED_COMPILER_EXPORT", "checked_commit": receipt["checked_commit"],
                          "implementation_state": receipt["implementation_state"], "RH": "OPEN", "Step4": "OPEN"}))
        return 0
    except (OSError, ValueError, TypeError, KeyError, subprocess.SubprocessError) as exc:
        failure = failure_envelope("compiler_receipt", exc)
        if not output_existed and args.output_dir.is_dir():
            target = args.output_dir/"failure.json"
            if not target.exists():
                target.write_text(json.dumps(failure, indent=2)+"\n", encoding="utf-8")
        print(json.dumps(failure, indent=2))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())

