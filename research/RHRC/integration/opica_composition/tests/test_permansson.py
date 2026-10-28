"""Frozen acceptance IDs: pure capability boundaries and actual durable dispatch."""
from copy import deepcopy
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from research.RHRC.permansson.opica_composition import (
 Action,select_action,validate_intervention,validate_policy_claim,qualify_provider,
 count_information_gain,require_comparable_experiments,PROVIDER_REPO,PROVIDER_COMMIT,PROVIDER_LEAN,SELECTED_APIS)
from research.RHRC.integration.opica_composition.canonical import ContractError
from research.RHRC.integration.opica_composition.journal import Journal
from research.RHRC.integration.opica_composition import provider
from research.RHRC.integration.opica_composition import qualification

SOURCE='a'*64
GENERATION='b'*64
PROFILE='c'*64


class PermanssonTests(unittest.TestCase):
    def choose(self,actions,ids,counts=None,budget=10):
        return select_action(actions,source=SOURCE,allowed_ids=frozenset(ids),attempt_counts=counts if counts is not None else {k:0 for k in ids},budget=budget)

    def test_t55(self):
        world={k:SOURCE for k in ('source','checker','profile','grammar','target_inventory')}
        validate_intervention(world,{**world,'priorities':'different'})
        for key in world:
            with self.subTest(key=key),self.assertRaises(ContractError):validate_intervention(world,{**world,key:'d'*64})

    def test_t56(self):
        self.assertEqual(self.choose([Action('unaffordable',SOURCE,9,11)],{'unaffordable'})['reason'],'NO_FEASIBLE_ACTION')

    def test_t57(self):
        with self.assertRaises(ContractError):self.choose([Action('unauthorized',SOURCE,9,1)],{'legal'})
        with self.assertRaises(ContractError):self.choose([Action('legal','d'*64,9,1)],{'legal'})

    def test_t58(self):
        claim={'mode':'POLICY_ADAPTER_ONLY','claim':'GLOBAL_SEARCH_OPTIMALITY','world':SOURCE,'menu':SOURCE,'history_revision':0,'budget':1}
        with self.assertRaises(ContractError):validate_policy_claim(claim)
        for field in ('source','checker','menu','budget','population','phase'):
            exp={k:SOURCE for k in ('source','checker','menu','budget','population','phase')}
            with self.subTest(field=field),self.assertRaises(ContractError):require_comparable_experiments(exp,{**exp,field:'changed'})

    def test_t59(self):
        env={'model_digest':SOURCE,'transition_atoms_digest':'d'*64}
        record={'repository':PROVIDER_REPO,'commit':PROVIDER_COMMIT,'toolchain':PROVIDER_LEAN,'environment':env,
          'apis':list(SELECTED_APIS),'raw_evidence':{n:{'consumer':'exact'} for n in SELECTED_APIS},'mode':'POLICY_ADAPTER_ONLY'}
        calls=[]
        result=qualify_provider(record,expected_environment=env,replay=lambda n,r:calls.append(n) or True)
        self.assertEqual(set(calls),set(SELECTED_APIS));self.assertFalse(result['host_theorem_authority'])
        bad=deepcopy(record);bad['environment']['model_digest']='e'*64
        with self.assertRaises(ContractError):qualify_provider(bad,expected_environment=env,replay=lambda *_:True)
        for name in SELECTED_APIS:
            with self.assertRaises(ContractError):qualify_provider(record,expected_environment=env,replay=lambda n,_:n!=name)

    def test_t60(self):
        actions=[Action('high',SOURCE,1000,1),Action('low',SOURCE,0,1)];counts={'high':0,'low':0}
        selected=[]
        for _ in range(8):
            x=self.choose(actions,set(counts),counts);selected.append(x['action_id']);counts[x['action_id']]+=1
        self.assertEqual(selected,['high','low']*4)
        self.assertEqual(self.choose([Action('new',SOURCE,1,20)],{'new'},budget=0)['kind'],'STOP')

    def test_t61(self):
        records=[{'source':SOURCE,'obligation':'o','status':'PROVED_CONDITIONAL','alias':str(i)} for i in range(20)]
        self.assertEqual(count_information_gain(records),1)
        self.assertEqual(count_information_gain(records+[{'source':SOURCE,'obligation':'debt','status':'ADAPTER_REQUIRED'}]),1)

    def test_t101(self):
        self.assertEqual(self.choose([],set()),{'schema':'OPICA_POLICY_CHOICE_V1','source':SOURCE,'mode':'POLICY_ADAPTER_ONLY','kind':'STOP','reason':'EMPTY_ELIGIBLE_MENU'})

    def test_t102(self):
        claim={'mode':'MODEL_VERIFIED_POLICY','claim':'DETERMINISTIC_SELECTION','world':SOURCE,'menu':SOURCE,'history_revision':0,'budget':1}
        with self.assertRaises(ContractError):validate_policy_claim(claim)
        self.assertEqual(provider.configuration()['mode'],'POLICY_ADAPTER_ONLY')

    def test_t106(self):
        x=self.choose([Action('STOP',SOURCE,1,1)],{'STOP'})
        self.assertEqual(x['kind'],'SELECT');self.assertEqual(x['action_id'],'STOP');self.assertNotIn('reason',x)

    def test_t107(self):
        with self.assertRaises(ContractError):self.choose([Action('one',SOURCE,1,1)],{'one','two'})
        with self.assertRaises(ContractError):self.choose([],{'one'})
        with self.assertRaises(ContractError):self.choose([Action('one',SOURCE,1,1)],{'one'},{'one':0,'forged':0})

    def test_t108(self):
        base=Path(os.environ.get('OPICA_TEST_TMP',str(provider.HOST.parent)))
        with tempfile.TemporaryDirectory(prefix='opica-policy-',dir=base) as tmp:
            path=Path(tmp)/'journal.db'
            with Journal(path) as j:
                j.activate(GENERATION,SOURCE,PROFILE,expected_revision=0)
                j.freeze_menu([Action('high',SOURCE,99,1),Action('low',SOURCE,0,1)],frozenset({'high','low'}),generation=GENERATION,source=SOURCE,expected_revision=1)
                first=j.dispatch({'high':'d'*64,'low':'e'*64},10,generation=GENERATION,source=SOURCE,expected_revision=2)
                self.assertEqual(first['action_id'],'high')
            with Journal(path) as j:
                self.assertEqual(j.attempt_counts(GENERATION),{'high':1,'low':0})
                with self.assertRaises(ContractError):j.dispatch({'high':'d'*64,'low':'e'*64},10,generation=GENERATION,source=SOURCE,expected_revision=2)
                second=j.dispatch({'high':'d'*64,'low':'e'*64},10,generation=GENERATION,source=SOURCE,expected_revision=3)
                self.assertEqual(second['action_id'],'low')
                j.db.execute('DELETE FROM attempts')
                with self.assertRaises(ContractError):j.dispatch({'high':'d'*64,'low':'e'*64},10,generation=GENERATION,source=SOURCE,expected_revision=4)

    def test_selected_audit_rejects_metadata_only_and_unapproved_axioms(self):
        with self.assertRaises(ContractError):provider.parse_audit(b'{}')
        rows=[]
        for api in provider.configuration()['apis']:
            rows.append(provider.MARKER+__import__('json').dumps({**api,'type_expression':'actual','consumer_type_expression':'actual','proof_value_expression':'actual','axioms':['sorryAx'],'consumer_axioms':[]}))
        rows.append(provider.MODULE_MARKER+__import__('json').dumps([provider.MODULE]))
        with self.assertRaises(ContractError):provider.parse_audit(('\n'.join(rows)).encode())

    def test_recorded_producer_root_is_metadata_not_artifact_location(self):
        self.assertEqual(str(provider.recorded_producer_root('/tmp/original/producer')),'/tmp/original/producer')
        self.assertEqual(str(provider.recorded_producer_root('C:\\native\\producer')),'C:\\native\\producer')
        for path in ('relative/producer','/tmp/../source','/tmp/producer/'):
            with self.assertRaises(ContractError):provider.recorded_producer_root(path)

    def test_current_compatibility_retains_exact_frozen_population(self):
        rows=qualification.frozen_atlas(provider.HOST)
        self.assertEqual(len(rows),462);self.assertEqual(sum(len(r['memberships']) for r in rows),696)
        self.assertEqual(sum(qualification.COHORTS[k] for k in ('OPICA_ORIGINAL76','OPICA_FOLLOWUP100','OPICA_ROUND2_40','OPICA_ROUND3_5')),221)
        source=qualification.atlas_driver(rows[:16]);self.assertEqual(source.count('declaration :='),16)
        self.assertIn('OpicaRound3AtlasExport.exportAtlas',source)

    def test_native_preparation_requires_linux_before_creating_outputs(self):
        target=provider.HOST.parent/'qualification-must-not-exist'
        self.assertFalse(target.exists())
        with patch.object(qualification.platform,'system',return_value='Windows'):
            with self.assertRaisesRegex(ContractError,'requires Linux'):qualification.prepare_native(provider.HOST,target)
        self.assertFalse(target.exists())


if __name__=='__main__':unittest.main()
