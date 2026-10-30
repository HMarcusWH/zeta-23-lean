"""Reviewed configuration checks; registration never grants theorem authority."""
from __future__ import annotations
from pathlib import Path
from .canonical import require,load_bytes
from .snapshot import file_hash
from .accept import ROUND4_LANES,REPLAY_GROUP_IDS,group_lanes
from .testing import checked_inventory
from ..opica_round4.math_gate import (EXPECTED_DECLARATIONS, BASELINE_EXPECTED_DECLARATIONS,
    BASELINE_MODULES, BASELINE_DECLARATION_COUNT, BASELINE_MODULE_COUNT,
    retained_support_scope, SOURCE_CONSTRAINT_MODULES, public_declarations)

def check_source_constraints(repo):
    repo=Path(repo);r4=repo/'research/RHRC/integration/opica_round4'
    ledger=load_bytes((r4/'SOURCE_CONSTRAINTS.json').read_bytes())
    require(ledger['schema']=='OPICA4_SOURCE_CONSTRAINTS_V1' and
            ledger['authority']=='SOURCE_BOUND_RESEARCH_REGISTER_NOT_PROOF_RECEIPT' and
            ledger['RH']=='OPEN' and ledger['Step4']=='OPEN','Source-constraint claim authority differs')
    require(set(ledger['current_modules'])==set(SOURCE_CONSTRAINT_MODULES),
            'Exact source-constraint module inventory differs')
    for module,row in ledger['current_modules'].items():
        path=module.replace('.','/')+'.lean'
        require(row['path']==path and file_hash(repo/path)==row['sha256'] and
                row['declarations']==public_declarations((repo/path).read_text(encoding='utf-8')),
                'Source-constraint definition or declaration binding differs')
    require(len(ledger['reference_source_sha256'])==42,'Exact mathematical source-reference census differs')
    for path,expected in ledger['reference_source_sha256'].items():
        require(path.startswith('Zeta23/') and path.endswith('.lean') and '..' not in Path(path).parts and
                file_hash(repo/path)==expected,'Source-constraint reference binding differs')
    require([row['id'] for row in ledger['property_comparison']]==['F'+str(i).zfill(2) for i in range(1,17)],
            'Exact sixteen-family property inventory differs')
    require({row['id'] for row in ledger['open_arithmetic_targets']}==
            {'C_DIRECT','C_SMOOTH_SCHUR','D_STRICT_EVEN','D_STRICT_ODD','D_SHARED'},
            'Arithmetic frontier alternatives changed')
    return {'status':'PASS_SOURCE_BINDINGS_ONLY','RH':'OPEN','Step4':'OPEN'}

def check_replay_partition(matrix):
    expected={'schema':'OPICA4_FIXED_REPLAY_PARTITION_V1',
              'groups':{group:list(group_lanes(group)) for group in REPLAY_GROUP_IDS},
              'original_lanes':list(ROUND4_LANES),'final_requires':['lanes','independent'],
              'mode':'MANDATORY_FULL_REPLAY_GROUPS_THEN_COMPLETE_JOIN',
              'authority':'CI_BOUND_NO_STANDALONE_REPORT_AUTHORITY',
              'native_workers_unchanged':True}
    require(matrix.get('independent_replay_partition')==expected,
            'Exact complete independent replay partition differs')
    return expected


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
    check_replay_partition(matrix)
    requirements=load_bytes((r4/'BASELINE_REQUIREMENTS.json').read_bytes())['requirements']
    require(len(requirements)==42 and len({r['id'] for r in requirements})==42,'Exact42 requirement inventory differs')
    packages=load_bytes((r4/'WORK_PACKAGES.json').read_bytes())['packages']
    require([r['id'] for r in packages]==['R4-'+str(i).zfill(2) for i in range(13)],'All13 work packages required')
    root_doc=load_bytes((r4/'ROOTS.json').read_bytes());roots=root_doc['roots']
    require(len(roots)==len(EXPECTED_DECLARATIONS) and
            {r['declaration'] for r in roots}==set(EXPECTED_DECLARATIONS),
            'Exact current supporting declaration inventory required')
    baseline=root_doc['historical_subset']
    require(baseline['declaration_count']==BASELINE_DECLARATION_COUNT==98 and
            baseline['module_count']==BASELINE_MODULE_COUNT==16 and
            baseline['declarations']==BASELINE_EXPECTED_DECLARATIONS and
            baseline['modules']==BASELINE_MODULES,'Original 98/16 support subset changed')
    integration=retained_support_scope()
    require(all(root_doc['integration_subset'].get(key)==value for key,value in integration.items()),
            'Retained 397/40 integration register differs')
    check_source_constraints(repo)
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
            'new_support_declarations':len(EXPECTED_DECLARATIONS),
            'retained_support_declarations':BASELINE_DECLARATION_COUNT,
            'retained_support_modules':BASELINE_MODULE_COUNT,
            'work_packages':13,'historical_connections':17,'RH':'OPEN','Step4':'OPEN'}
