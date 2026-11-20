"""Audit compiler proof-value reachability and separately verify pinned source calls."""

from collections import deque
from functools import cache
import json
from pathlib import Path
import re
import subprocess
import sys


PIN = 'c867a8f15320ad6ac69177e0a498de4cb9d744f9'
TREE = '573cda1f06d2d7a0e61349a53183311e4ba621fc'
GRAPH = 'research/RHRC/graph/generated/'
GIT = ['git', '--no-lazy-fetch', '-C', sys.argv[1]]
BASE = 'https://github.com/HMarcusWH/zeta-23-lean/blob/' + PIN + '/'
SEEDS = {
    'divisor': 'Zeta23.CCM.native_divisor_coefficient_identity',
    'weighted divisor': 'Zeta23.CCM.native_weighted_dirichlet_identity',
    'weighted inversion': 'Zeta23.OPICAFollowup.weighted_mobius_inverse',
    'squarefree omission': 'Zeta23.OPICARound2.native_squarefree_omission_bound',
    'Mobius probe': 'Zeta23.OPICARound2.native_mobius_probe_inverse',
}
ENDS = {
    'fiber': 'Zeta23.CCM.nativeIntegerPrimePair_fiber',
    'literal drive': 'Zeta23.CCM.nativeIntegerTranslateAction_primeField_eq_integerDriveField',
    'original prime integral': 'Zeta23.ExceptionalZero.riemannHypothesis_of_originalPrimeField_allDampedIntegral',
    'input range': 'Zeta23.ExceptionalZero.riemannHypothesis_of_nativeInput_allRangeClosure',
    'Step 4 AX': 'Zeta23.ExceptionalZero.riemannHypothesis_of_step4_AX',
    'visible pole': 'Zeta23.OPICAFollowup.nativePrimeField_visiblePole',
}
SOURCE = {
    'Zeta23.OPICARound4.weighted_convolution': 'Zeta23/OPICARound4/MobiusHyperbola.lean',
    'Zeta23.OPICARound4.vonMangoldt_weighted_is_hyperbolaU': 'Zeta23/OPICARound4/MobiusHyperbola.lean',
    'Zeta23.OPICARound4.finite_vonMangoldt_hyperbola_half': 'Zeta23/OPICARound4/MobiusHyperbola.lean',
    'Zeta23.OPICARound4.actualCorrelationPrimeField_hyperbola_half': 'Zeta23/OPICARound4/ActualSourceHyperbola.lean',
    'Zeta23.OPICARound4.actualCorrelationPrimeField_add_longTerm_rapid_bound': 'Zeta23/OPICARound4/ActualSourceHyperbola.lean',
    'Zeta23.OPICARound4.riemannHypothesis_of_actualCorrelationLongTerm_eventual_lower': 'Zeta23/OPICARound4/ActualSourceHyperbola.lean',
    'Zeta23.XiPrime.prime_of_isPrimePow_dvd_squarefree': 'Zeta23/XiPrime/Coeff/MainTerm/Squarefree.lean',
    'Zeta23.OPICARound4.weighted_mobius_inverse': 'Zeta23/OPICARound4/MobiusHyperbola.lean',
    'Zeta23.OPICARound4.hyperbolaT_negative_test': 'Zeta23/OPICARound4/MobiusHyperbola.lean',
    'Zeta23.OPICARound4.actualCorrelationLongTerm_eventual_lower_iff_combined': 'Zeta23/OPICARound4/ActualSourceHyperbola.lean',
}


def read(path):
    return subprocess.check_output(GIT + ['show', PIN + ':' + path])


@cache
def lean_lines(path):
    return read(path).decode('utf-8-sig').splitlines()


def signature(path, qualified):
    short = qualified.rsplit('.', 1)[1]
    lines = lean_lines(path)
    head = re.compile(r'^(?:theorem|lemma) ' + re.escape(short) + r'(?:\s|$)')
    start = next(i for i, line in enumerate(lines) if head.match(line))
    stop = next(i for i in range(start, len(lines)) if ':=' in lines[i])
    return {'name': qualified, 'url': BASE + path + '#L' + str(start+1),
            'signature': '\n'.join(lines[start:stop] + [lines[stop].partition(':=')[0].rstrip()]).rstrip()}


def bfs(start, graph):
    seen = {start: None}
    queue = deque([start])
    while queue:
        here = queue.popleft()
        for target in graph[here]:
            if target not in seen:
                seen[target] = here
                queue.append(target)
    return seen


def main():
    actual_tree = subprocess.check_output(GIT + ['rev-parse', PIN+'^{tree}']).decode().strip()
    assert actual_tree == TREE
    vertices = [json.loads(row) for row in read(GRAPH + 'lean_declarations.jsonl').splitlines()]
    names = {v['id']: i for i, v in enumerate(vertices)}
    index = {v['declaration']: i for i, v in enumerate(vertices)}
    reverse = [[] for _ in vertices]
    rows = exact = value_rows = type_only = 0
    for shard in '0123456789abcdef':
        for raw in read(GRAPH + 'relations/relations-' + shard + '.jsonl').splitlines():
            rows += 1
            edge = json.loads(raw)
            if edge['kind'] == 'USES_CONSTANT' and edge['provenance'] == 'LEAN_ENV_EXACT':
                exact += 1
                if edge['used_in_value']:
                    value_rows += 1
                    reverse[names[edge['target']]].append(names[edge['source']])
                else:
                    type_only += 1
    reverse = [sorted(set(r), key=lambda i: vertices[i]['declaration']) for r in reverse]
    paths = {label: bfs(index[name], reverse) for label, name in {**SEEDS, **ENDS}.items()}
    def spell(path):
        return [vertices[i]['declaration'] for i in path]
    def witness(label, end):
        dest = index[ENDS[end]]
        if dest not in paths[label]:
            return None
        result = []
        while dest is not None:
            result.append(dest)
            dest = paths[label][dest]
        return spell(reversed(result))
    results = {}
    for label, name in SEEDS.items():
        results[label] = {'direct_uses_by': len(reverse[index[name]]),
                          'direct_consumers': spell(reverse[index[name]]),
                          'all_transitive_consumers_excluding_self': len(paths[label])-1,
                          'paths_to_tested_consumers': {end: witness(label, end) for end in ENDS}}
    pairs = [('divisor','weighted divisor'), ('weighted divisor','weighted inversion'), ('weighted divisor','squarefree omission'),
             ('weighted inversion','Mobius probe'), ('weighted inversion','squarefree omission')]
    common = {}
    for a,b in pairs:
        both = [i for i in paths[a].keys() & paths[b].keys() if i not in [index[SEEDS[a]],index[SEEDS[b]]] and not vertices[i]['private_or_internal'] and vertices[i]['repository_scope']!='EXTERNAL']
        common[a+' + '+b] = {'public_project_consumers':len(both),'first_alphabetical': sorted(spell(both))[:5]}
    declarations = {}
    for name in list(SEEDS.values())+list(ENDS.values())+list(SOURCE):
        v = vertices[index[name]] if name in index else None
        file = SOURCE[name] if name in SOURCE else v['module'].replace('.','/')+'.lean'
        declarations[name] = {**signature(file,name),'present_in_committed_registry':v is not None}
    chain = list(SOURCE)[:6]
    source_edges = []
    for prior, later in zip(chain, chain[1:]):
        lines = lean_lines(SOURCE[later]); start=int(declarations[later]['url'].split('#L')[1])-1
        next_decl = next((i for i in range(start+1,len(lines)) if re.match(r'^(?:(?:private|noncomputable) )?(?:lemma|theorem|def|end)\b',lines[i])),len(lines))
        word=re.compile(r'\b'+re.escape(prior.rsplit('.',1)[1])+r'\b')
        calls=[{'url':BASE+SOURCE[later]+'#L'+str(i+1),'text':lines[i].strip()} for i in range(start,next_decl) if word.search(lines[i])]
        assert calls
        source_edges.append({'from_dependency':prior,'to_consumer':later,'literal_source_calls':calls})
    return {'commit':PIN,'tree':TREE,'declaration_count':len(vertices),'relation_rows':rows,
            'lean_env_exact_uses_constant_rows':exact,'type_only_rows':type_only,'value_rows':value_rows,
            'distinct_directed_value_edges':sum(map(len,reverse)), 'registered_seed_consumer_comparison':results,
            'common_consumers':common,'declarations':declarations,'additional_source_only_chain':source_edges,
            'mathematical_readout': [
                'The genuine weighted prime-power divisor identity feeds native completion and the original-prime all-damped L2/integral implications. The shortest AX witness passes through a theorem requiring prime-field MemLp. Its terminal premise remains NativeOriginalPrimeFieldAllDampedIntegral.',
                'The registered Followup weighted_mobius_inverse uses exponent a > 1/2 and a separately supplied finite mixing moment. It differs from the Round4 finite weighted_mobius_inverse in the pinned source. The squarefree omission bound requires 0 < k <= 2047 and a vanished coefficient of a finite probe vector.',
                'The separate five-edge source chain connects actual finite Mobius flattening to RH under an eventual lower on the actual long term. Its pinned equivalence retains the rank-one plus full signed off-diagonal. A signed sum over older ordinary primes or a large positive and negative factorial mass requires an independent transfer to this normalized functional and an upper/lower at the quantifiers in the source; the formal graph supplies neither automatically.',
                'A concrete generic counterexample in the pinned source makes hyperbolaT negative at cutoff one for a signed test. It excludes a general positivity inference and does not reject the actual fixed-source bound.'
            ],
            'scope':'Graph reachability follows dependency to user and includes values of definitions and proofs. Source-only calls are checked literally in pinned Lean proof bodies and are not attributed to the compiler graph. Null paths describe this graph only. No build or proof gate was run.'}


if __name__ == '__main__':
    result=main()
    output=Path(__file__).with_name('DIVISOR_CONSUMER_GRAPH.json')
    output.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(result['distinct_directed_value_edges'])
    for label,r in result['registered_seed_consumer_comparison'].items():
        print(label, r['direct_uses_by'],r['all_transitive_consumers_excluding_self'],
              {k:len(p)-1 for k,p in r['paths_to_tested_consumers'].items() if p})
    print(result['common_consumers'])
