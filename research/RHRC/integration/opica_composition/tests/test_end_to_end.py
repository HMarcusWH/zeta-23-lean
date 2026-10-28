from pathlib import Path
from dataclasses import replace
import tempfile,unittest,uuid,hashlib
from research.RHRC.integration.opica_composition.campaign import require_hidden_partition,run_bounded_campaign
from research.RHRC.integration.opica_composition.canonical import ContractError,load_bytes,require
from research.RHRC.integration.opica_composition.contracts import CompositionProposal
from research.RHRC.integration.opica_composition.journal import Journal,replay_events
from research.RHRC.permansson.opica_composition import require_comparable_experiments,Action
from research.RHRC.ffbbp.opica_composition import assess_composition_reduction,deduplicate_evidence_origins

class EndToEndTests(unittest.TestCase):
    def test_t62(self):
        with self.assertRaises(ContractError):require_hidden_partition({'partition':'CONSTRUCTION','retrieved_ids':['answer']},
            {'partition':'CONFIRMATORY_FROZEN','gold_ids':['answer']})
    def test_t63(self):
        a={'source':'s','checker':'c','menu':'m','budget':1,'population':'p','phase':'CONFIRMATORY_FROZEN'}
        with self.assertRaises(ContractError):require_comparable_experiments(a,{**a,'budget':10})
    def test_t73(self):
        # Actual full D02-to-D05 term, independently replayed and durably published.
        # Native source/config absence is an error, never a skipped test.
        from research.RHRC.integration.opica_composition.tests.test_executor import native_context,calibration
        from research.RHRC.integration.opica_composition.proposals import calibration_plan
        from research.RHRC.integration.opica_composition.descendant import validate_descendant
        worker,snapshot,root=native_context()
        require(worker.production is True,'Linux isolated end-to-end qualification required')
        validate_descendant(Path(snapshot.repo),require_clean=True)
        snapshot=replace(snapshot,source_policy='REVIEWED_FROZEN')
        target,artifacts,_=calibration('D05')
        names=('Zeta23.OPICARound3.cofinally_both_neutral_negative_of_off_line_zero',
               'Zeta23.OPICARound3.first_simultaneous_newborn_source_witnesses','And.intro','Exists.intro')
        ids={name:hashlib.sha256(name.encode()).hexdigest() for name in names}
        plan=calibration_plan({'D02':ids[names[0]],'D05':ids[names[1]],'And.intro':ids[names[2]],'Exists.intro':ids[names[3]]},'D05')
        proposal=CompositionProposal('full-native-round4',target.target_id,snapshot.generation,plan)
        table=load_bytes((Path(artifacts.output)/'constant-table.json').read_bytes())
        out=root/('campaign-'+uuid.uuid4().hex)
        result=run_bounded_campaign(snapshot=snapshot,targets={'D02_D05':target},proposals={'D02_D05':proposal},
            constant_tables={'D02_D05':table},output=out,worker=worker,budget=1,priorities={'D02_D05':{'priority':1,'cost':1}})
        self.assertEqual(result['published_applications'],1)
        events=replay_events((out/'EVENTS.jsonl').read_bytes())
        self.assertTrue(any(r['kind']=='APPLICATION_VERIFIED' for r in events))
        self.assertEqual(result['Step4'],'OPEN')
        # A second durable iteration may independently check the same proposal.
        # Keep both execution records, resolve each attempt exactly, and export
        # one mathematical edge. No test-issued proof capability is used.
        from research.RHRC.integration.opica_composition.contracts import AttemptArtifacts
        from research.RHRC.integration.opica_composition.journal import publish_verified_application
        from research.RHRC.integration.opica_composition.applications import application_from_publication
        from research.RHRC.integration.opica_composition.views import export_state
        prior=next(r['payload']['attempt_id'] for r in events if r['kind']=='APPLICATION_VERIFIED')
        raw=AttemptArtifacts.from_bytes((out/'attempts'/prior/'receipt.json').read_bytes())
        with Journal(out/'journal.db',repository=Path(snapshot.repo)) as journal:
            state=journal.state()
            next_choice=journal.dispatch({'D02_D05':proposal.digest},1,generation=snapshot.generation,
                source=snapshot.source_digest,expected_revision=state['revision'])
            publish_verified_application(journal,next_choice['attempt_id'],raw,snapshot,target,worker=worker,
                generation=snapshot.generation,source=snapshot.source_digest,expected_revision=next_choice['revision'])
            first=application_from_publication(journal,prior)
            second=application_from_publication(journal,next_choice['attempt_id'])
            self.assertEqual(first['id'],second['id'])
            views=export_state(journal)
            self.assertEqual(len(views['APPLICATIONS.jsonl'].splitlines()),1)
            self.assertEqual(len(journal.current_applications()),2)
    def test_t93(self):
        with self.assertRaises(ContractError):assess_composition_reduction([{'id':'x','gold':'answer'}],('gold',),lambda _:True)
    def test_t99(self):
        rows=[{'source':'same','invocation':'native-once','raw_sha256':'a'*64,'framework':f} for f in ('FFBBP','OoL','Permansson')]
        self.assertEqual(len(deduplicate_evidence_origins(rows)),1)
    def test_t117(self):
        with tempfile.TemporaryDirectory() as td:
            with Journal(Path(td)/'journal.db') as j:
                j.activate('a'*64,'b'*64,'c'*64,expected_revision=0)
                j.freeze_menu([Action('STOP','b'*64,1,1)],frozenset({'STOP'}),generation='a'*64,source='b'*64,expected_revision=1)
                expected_revision=j.state()['revision']
                d=j.dispatch({'STOP':'d'*64},1,generation='a'*64,source='b'*64,expected_revision=expected_revision)
                self.assertEqual(d['kind'],'SELECT');self.assertEqual(d['action_id'],'STOP')
                with self.assertRaises(ContractError):j.dispatch({'STOP':'d'*64},2,generation='a'*64,source='b'*64,expected_revision=expected_revision)

if __name__=='__main__':unittest.main()
