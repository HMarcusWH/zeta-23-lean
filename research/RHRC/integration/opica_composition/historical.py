"""Read-only historical input conversion, preserving negative/open dispositions."""
from __future__ import annotations
from pathlib import Path
from .canonical import require, load_bytes, digest

def load_historical_inputs(paths: list[Path]) -> list[dict]:
    rows=[]
    for path in paths:
        data=Path(path).read_bytes();value=load_bytes(data)
        rows.append({'path':str(path),'scope':'HISTORICAL_ONLY','content_digest':digest(value,domain='OPICA_HISTORY_V1'),
                     'record':value,'current_proof_authority':False})
    return rows

def reviewed_connections(overlay: dict) -> list[dict]:
    rows=overlay.get('connections',overlay.get('semantic_connections'))
    require(type(rows)is list and len(rows)==17,'exact authored seventeen-connection inventory required')
    require(len({r['id'] for r in rows})==17,'duplicate connection identity')
    return rows

def preserve_dispositions(expected: list[dict], observed: list[dict]) -> None:
    require(len(expected)==len(observed) and {r['id'] for r in expected}=={r['id'] for r in observed},
            'connection inventory differs')
    by_id={r['id']:r for r in observed}
    for row in expected:
        key='disposition' if 'disposition' in row else 'status'
        require(by_id[row['id']].get(key)==row.get(key),'historical disposition was coerced positive')
