import sqlite3
from pathlib import Path
import tempfile
import unittest
from research.RHRC.integration.opica_composition.journal import Journal,replay_events,require_revival
from research.RHRC.integration.opica_composition.canonical import ContractError
from research.RHRC.permansson.opica_composition import Action

class JournalTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.path=Path(self.tmp.name)/'state.db'
        self.j=Journal(self.path);self.j.activate('a'*64,'b'*64,'c'*64,expected_revision=0)
    def tearDown(self):self.j.close();self.tmp.cleanup()
    def menu(self):
        self.j.freeze_menu([Action('one','b'*64,5,1),Action('two','b'*64,2,1)],frozenset({'one','two'}),generation='a'*64,source='b'*64,expected_revision=1)
    def dispatch(self,revision=2):
        return self.j.dispatch({'one':'d'*64,'two':'e'*64},10,generation='a'*64,source='b'*64,expected_revision=revision)
    def test_t51(self):
        self.menu();d=self.dispatch();self.j.record_outcome(d['attempt_id'],'ADAPTER_REQUIRED',{'missing':'normalization'},generation='a'*64,source='b'*64,expected_revision=3)
        before=self.j.export_events();self.j.close();self.j=Journal(self.path)
        self.assertEqual(before,self.j.export_events());self.assertEqual(len(replay_events(before)),4)
        self.j.invalidate('changed source',generation='a'*64,source='b'*64,expected_revision=4)
        self.j.activate('f'*64,'1'*64,'c'*64,expected_revision=5)
        self.assertEqual(self.j.current_applications(),[])
    def test_t52(self):
        self.menu();d=self.dispatch();self.j.invalidate('newsource',generation='a'*64,source='b'*64,expected_revision=3)
        self.j.activate('f'*64,'1'*64,'c'*64,expected_revision=4)
        with self.assertRaises(ContractError):self.j.record_outcome(d['attempt_id'],'UNRESOLVED',{},generation='a'*64,source='b'*64,expected_revision=5)
        self.j.archive({'old_attempt':d['attempt_id']},expected_revision=5)
        self.assertEqual(self.j.current_applications(),[])
    def test_t53(self):
        require_revival({'blocker':'range','premise_digest':'a'*64},{'blocker':'range','premise_digest':'b'*64},'c'*64)
    def test_t54(self):
        with self.assertRaises(ContractError):require_revival({'blocker':'range','premise_digest':'a'*64},{'blocker':'range','premise_digest':'a'*64,'renamed':'new'},'c'*64)
    def test_t89(self):
        self.menu();d=self.dispatch();self.j.invalidate('race',generation='a'*64,source='b'*64,expected_revision=3)
        from research.RHRC.integration.opica_composition.journal import _PUBLISH
        with self.assertRaisesRegex(ContractError,'stale journal revision'):
            self.j._publish(_PUBLISH,d['attempt_id'],{'status':'PROVED_CONDITIONAL','publication_eligible':True,
                'source_generation':'a'*64},generation='a'*64,source='b'*64,expected_revision=3)
        self.assertEqual(self.j.current_applications(),[])
    def test_t90(self):
        self.j.invalidate('correction',generation='a'*64,source='b'*64,expected_revision=1)
        with self.assertRaises(ContractError):self.j.activate('a'*64,'b'*64,'c'*64,expected_revision=2)
    def test_dispatch_is_durable_and_fair(self):
        self.menu();first=self.dispatch();self.assertEqual(first['action_id'],'one')
        self.j.close();self.j=Journal(self.path);second=self.dispatch(3)
        self.assertEqual(second['action_id'],'two');self.assertEqual(self.j.attempt_counts('a'*64),{'one':1,'two':1})
    def test_forged_count_projection_fails_restart(self):
        self.menu();self.dispatch();self.j.db.execute('DELETE FROM attempts')
        with self.assertRaises(ContractError):self.j.verify_chain()
    def test_cas_failure_is_atomic(self):
        self.menu();before=self.j.export_events()
        with self.assertRaises(ContractError):self.dispatch(1)
        self.assertEqual(before,self.j.export_events())
    def test_nonproof_status_cannot_publish(self):
        self.menu();d=self.dispatch()
        with self.assertRaises(ContractError):self.j.record_outcome(d['attempt_id'],'PROVED_CONDITIONAL',{'PASS':True},generation='a'*64,source='b'*64,expected_revision=3)

if __name__=='__main__':unittest.main()
