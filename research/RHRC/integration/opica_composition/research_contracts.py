"""Scientific authority is independent of process status and package validity."""
from __future__ import annotations
from .canonical import require, digest_text

LABELS=frozenset({'PROVED','DERIVED','LEAD / HYPOTHESIS','EXPERIMENTAL SIGNAL','OPEN','FALSIFIED','UNRESOLVED'})

def validate_research_contract(row: dict) -> None:
    fields={'id','statement','source','witness','quantifiers','domain','normalization','status','consumer','missing_premises'}
    require(set(row)>=fields,'incomplete research contract')
    require(row['status'] in LABELS,'unknown authority label')
    require(type(row['quantifiers']) is list and type(row['missing_premises']) is list,'ordered quantifiers/open premises required')
    if row['status']=='PROVED':
        require(row.get('native_receipt') and row.get('axiom_receipt') and row.get('independent_consumer'),
                'paper/schema result cannot be promoted to PROVED')
    if row.get('terminal'):
        require(row.get('independent_source_estimate') is True or row['status']!='PROVED',
                'terminal condition has not been independently established')

def require_same_state(expected: dict, actual: dict) -> None:
    for field in ('source','aperture','cutoff','parity','witness','normalization','domain','quantifiers'):
        require(field in expected and actual.get(field)==expected[field], 'same-state adapter required: '+field)
