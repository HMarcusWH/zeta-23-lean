"""Reviewed configuration checks; registration never grants theorem authority."""
from __future__ import annotations
from pathlib import Path
from .canonical import require,load_bytes
from .snapshot import file_hash
from .accept import ROUND4_LANES
from .testing import checked_inventory

def check_configuration(repo):
    repo=Path(repo);here=repo/'research/RHRC/integration/opica_composition';r4=here.parent/'opica_round4'
    profile=load_bytes((here/'PROFILE.json').read_bytes())
    require(profile['profile_id']=='ROUND4_GOVERNED_DEDUCTION_V1' and
            profile['retained_profile']=='THREE_FRAMEWORK_INTEGRATED_V1','Profile escalation or missing retained release')
    require(profile['required_input_lanes']==list(ROUND4_LANES) and profile['aggregate_lane']=='ACCEPTANCE',
            'Exact eleven-input aggregate required')
    require(profile['RH']=='OPEN' and profile['Step4']=='OPEN' and profile['human_review']=='NOT_ESTABLISHED','Claim firewall changed')
    contract=load_bytes((here/'BUILD_CONTRACT.json').read_bytes())
    for row in contract['baseline_files']:
        require(file_hash(r4/row['path'])==row['sha256'],'Immutable corrected-kit baseline changed')
    original=load_bytes((r4/'BASELINE_ACCEPTANCE_MATRIX.json').read_bytes())['tests']
    inventory=checked_inventory()['tests'];by_case={r['case']:r for r in inventory if r['case']}
    require(len(original)==117 and set(by_case)=={r['id'] for r in original},'Original117-case census differs')
    matrix=load_bytes((r4/'ACCEPTANCE_MATRIX.json').read_bytes())
    require(matrix['original_cases']==original,'Original case meaning changed')
    require(matrix['implemented_methods']==inventory,'Exact test method-to-lane register differs')
    requirements=load_bytes((r4/'BASELINE_REQUIREMENTS.json').read_bytes())['requirements']
    require(len(requirements)==42 and len({r['id'] for r in requirements})==42,'Exact42 requirement inventory differs')
    packages=load_bytes((r4/'WORK_PACKAGES.json').read_bytes())['packages']
    require([r['id'] for r in packages]==['R4-'+str(i).zfill(2) for i in range(13)],'All13 work packages required')
    roots=load_bytes((r4/'ROOTS.json').read_bytes())['roots']
    require(len(roots)==98 and len({r['declaration'] for r in roots})==98,'Exact98 new supporting declarations required')
    for row in roots:require(row['module'].replace('.','/')+'.lean'==row['path'] and (repo/row['path']).is_file(),'Root origin differs')
    targets=load_bytes((here/'PUBLIC_TARGETS.json').read_bytes())
    require([r['id'] for r in targets['calibration']]==['D02_D05','D02_D04'],'Both full calibration targets required')
    from .historical import reviewed_connections,preserve_dispositions
    old=load_bytes((r4.parent/'opica_round3/atlas/SEMANTIC_OVERLAY.json').read_bytes())
    retained=load_bytes((r4/'RESEARCH_DISPOSITIONS.json').read_bytes())
    preserve_dispositions(reviewed_connections(old),retained['historical_connections'])
    for document in ('CLOSURE_OBLIGATIONS.json','MATH_CONTRACTS.json','INPUT_REGISTER.json'):
        row=load_bytes((r4/document).read_bytes());require(row['RH']=='OPEN' and row['Step4']=='OPEN','Research registration escalated a claim')
    return {'schema':'OPICA4_CONFIGURATION_CHECK_V1','status':'PASS_CONTRACT_ONLY','requirements':42,
            'mandatory_requirements':41,'baseline_cases':117,'registered_test_methods':len(inventory),
            'new_support_declarations':98,'work_packages':13,'historical_connections':17,'RH':'OPEN','Step4':'OPEN'}
