"""Independent structural checks; does not import repository graph code."""
from pathlib import Path
import json, hashlib, collections, subprocess, networkx as nx
R=Path('/mnt/data/rh_audit/snapshot/zeta-23-lean-main'); O=Path('/mnt/data/rh_audit/results')
G=R/'research/RHRC/graph/generated'
def rows(p): return [json.loads(l) for l in p.read_text().splitlines() if l.strip()]
nodefiles=['repository_files','lean_modules','lean_declarations','lean_source_declarations','registry_nodes']
nodes=[]
for n in nodefiles: nodes+=rows(G/(n+'.jsonl'))
ids=[n['id'] for n in nodes]; counts=collections.Counter(ids)
edges=rows(G/'relations.jsonl'); kinds=collections.Counter(e['kind'] for e in edges)
# Some nodes are in other generated records: enumerate endpoint-only IDs explicitly.
idset=set(ids); missing=sorted(set(e[k] for e in edges for k in ['source','target'])-idset)
print('NODE_COUNT',len(nodes),'DUPLICATES',sum(v-1 for v in counts.values()),'MISSING',len(missing));print(missing[:20]);print('KIND_COUNTS',dict(kinds))
# Registry_nodes includes repository and extra nodes? Report rather than invent missing records.
D=nx.DiGraph();I=nx.DiGraph()
for n in nodes:
 if n.get('type')=='LeanDeclaration': D.add_node(n['id'])
 if n.get('type')=='LeanModule': I.add_node(n['id'])
for e in edges:
 if e['kind']=='USES_CONSTANT': D.add_edge(e['source'],e['target'])
 if e['kind']=='IMPORTS': I.add_edge(e['source'],e['target'])
sccs=[sorted(c) for c in nx.strongly_connected_components(D) if len(c)>1]
loops=sorted(nx.nodes_with_selfloops(D))
ic=[sorted(c) for c in nx.strongly_connected_components(I) if len(c)>1]
claim_nodes=[n for n in nodes if n.get('type')=='RegisteredClaim']
claim_status={n['id']:n['projection']['status'] for n in claim_nodes}
proved=[e for e in edges if e['kind']=='PROVES'];bad_proved=[e for e in proved if claim_status.get(e['target'])!='PROVED_UNCONDITIONAL']
ph=R/'research/RHRC/integration/generated';res=rows(ph/'SOURCE_CANDIDATE_RESOLUTION.jsonl')
print('RES_KEYS',res[0].keys());print('RES_SAMPLE',res[0])
unresolved=[x for x in res if x.get('resolution_status')=='NO_COMPILER_MATCH' or x.get('visibility_class')=='UNRESOLVED_SOURCE_IDENTITY']
# Exact source file hash census independently matches original index.
files=rows(G/'repository_files.jsonl');print('FILE_KEYS',files[0])
tracked=set(subprocess.check_output(['git','ls-files','-z'],cwd=R).decode().strip('\x00').split('\x00'))
paths=set(n['path'] for n in files)
result={'scope':'INDEPENDENT_STATIC_GRAPH_AUDIT_NOT_LEAN_COMPILATION','node_count':len(nodes),'unique_node_count':len(idset),'duplicate_node_ids':[k for k,v in counts.items() if v>1],'relation_count':len(edges),'relation_kind_counts':dict(kinds),'duplicate_relation_ids':len(edges)-len({e['id'] for e in edges}),'missing_endpoints_from_all_node_files':missing,'file_count':len(files),'tracked_files_missing_from_graph':sorted(tracked-paths),'graph_files_not_in_index':sorted(paths-tracked),'dependency_nodes':D.number_of_nodes(),'dependency_edges':D.number_of_edges(),'dependency_nontrivial_sccs':sccs,'dependency_self_loops':loops,'import_nontrivial_sccs':ic,'import_self_loops':sorted(nx.nodes_with_selfloops(I)),'proves_edges':len(proved),'proves_open_or_unregistered':bad_proved,'open_claims':[k for k,v in claim_status.items() if v=='OPEN'],'unresolved_source_identities':unresolved}
(O/'independent_graph_audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['unresolved_source_identities','dependency_self_loops','missing_endpoints_from_all_node_files']},indent=2)[:16000]);print('SELF_LOOPS',loops[:20])
