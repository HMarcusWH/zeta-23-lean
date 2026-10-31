"""Explicit AND/OR closure obligations; OPEN leaves are never assumed true."""
from __future__ import annotations
from .canonical import require

def evaluate_closure(nodes: list[dict], root: str, *, verified_leaves: dict[str, str]) -> dict:
    by_id={r['id']:r for r in nodes}
    require(len(by_id)==len(nodes) and root in by_id,'closure node inventory invalid')
    active=set(); memo={}
    def walk(key):
        require(key in by_id and key not in active,'dangling/cyclic closure dependency')
        if key in memo:return memo[key]
        active.add(key);row=by_id[key];kind=row['kind']
        require(kind in {'LEAF','AND','OR'},'unknown closure operator')
        if kind=='LEAF':
            require(set(row)>={'id','kind','proposition','source','witness','quantifiers','consumers','status','next_test'},
                    'incomplete mathematical open leaf')
            state='PROVED' if verified_leaves.get(key)==row.get('proof_evidence') and row.get('proof_evidence') else 'OPEN'
            missing=[] if state=='PROVED' else [key]
        else:
            children=row['children'];require(children and len(children)==len(set(children)),'empty/duplicate logical branches')
            parts=[walk(k) for k in children]
            closed=all(p['status']=='PROVED' for p in parts) if kind=='AND' else any(p['status']=='PROVED' for p in parts)
            state='PROVED' if closed else 'OPEN';missing=[] if closed else sorted({x for p in parts for x in p['open_leaves']})
        active.remove(key);memo[key]={'status':state,'open_leaves':missing};return memo[key]
    result=walk(root)
    return {'root':root,**result,'scope':'CLOSURE_GRAPH_STATUS_ONLY','RH':'OPEN','Step4':'OPEN'}
