import unittest
from research.RHRC.integration.opica_composition.applications import checked_application,require_applicable
from research.RHRC.integration.opica_composition.canonical import ContractError

class ApplicationTests(unittest.TestCase):
    def test_empty_current_journal_exports_no_mathematical_edges(self):
        import tempfile
        from pathlib import Path
        from research.RHRC.integration.opica_composition.journal import Journal
        from research.RHRC.integration.opica_composition.views import export_state
        with tempfile.TemporaryDirectory() as tmp:
            with Journal(Path(tmp)/'journal.db') as journal:
                products=export_state(journal)
                self.assertEqual(products['APPLICATIONS.jsonl'],b'')
                self.assertEqual(products,export_state(journal))
    def test_forged_verified_flag_is_not_a_proof(self):
        with self.assertRaises(ContractError):
            checked_application({'status':'PROVED_CONDITIONAL','publication_eligible':True,'independent_replay':True},
                inputs=[],output='a'*64,substitutions={},witness_bindings={},open_premises=[])
    def test_shared_source_edge_is_not_implication(self):
        with self.assertRaises(ContractError):require_applicable({'kind':'SHARES_SOURCE'},source_generation='a'*64,
            authorized_context=[],supplied_propositions=set(),proof_registry={})
    def test_unpublished_application_rejected(self):
        with self.assertRaises(ContractError):require_applicable({'kind':'CHECKED_APPLICATION','source_generation':'a'*64,
            'context':[],'proof_evidence':'b'*64,'target_digest':'c'*64,'inputs':[],'open_premises':[]},
            source_generation='a'*64,authorized_context=[],supplied_propositions=set(),proof_registry={})

if __name__=='__main__':unittest.main()
