"""Independent native arithmetic replay and research-scope mutation controls."""
from copy import deepcopy
import json
from pathlib import Path
import tempfile
from unittest.mock import patch
import unittest
from research.RHRC.integration.opica_round4 import source_research as R


class SourceResearchTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.case=R.E.prescribed_cases()[0]
        cls.producer=R.evaluate_case(cls.case,256,'unit')
        cls.checker=R.evaluate_case(cls.case,512,'direct')

    def test_independent_carrier_and_source_replay(self):
        self.assertGreater(R.compare(self.producer,self.checker),40)

    def test_empty_negative_space_is_not_observation_evidence(self):
        self.assertTrue(self.producer['negative_observation_is_vacuous'])
        self.assertTrue(all(x['status']=='NEGATIVE_SUBSPACE_EMPTY' for x in self.producer['observation']))
        self.assertFalse(self.producer['gain_is_uniform_theorem'])

    def test_same_state_and_signed_costs_cannot_be_changed(self):
        for key in ['shift','actual_response','concentration_budget','signed_norm_trace_budget']:
            bad=deepcopy(self.producer);bad['states'][0][key]={'lower':'1000','upper':'1001'}
            with self.assertRaises(R.B.InvalidRequest):R.compare(bad,self.checker)

    def test_wrong_odd_input_or_source_kind_is_rejected(self):
        bad=deepcopy(self.producer);bad['states'][1]['input_kind']='EVEN_RAY_SUBSTITUTION'
        with self.assertRaises(R.B.InvalidRequest):R.compare(bad,self.checker)

    def test_campaign_summary_source_and_authority_cannot_be_promoted(self):
        cases=R.E.prescribed_cases()
        base={'schema':'OPICA4_SOURCE_RESEARCH_CAMPAIGN_V1','status':'PASS_REPRODUCIBLE_FINITE_RESEARCH',
            'source_identity':R.identity(),'RH':'OPEN','Step4':'OPEN',
            'authority':'INDEPENDENT_FINITE_RESEARCH_REPLAY_NOT_UNIFORM_ARITHMETIC',
            'cases':[{'id':c['id'],'source_kind':c['source']['kind']} for c in cases]}
        for field in ('authority','source_kind'):
            with tempfile.TemporaryDirectory() as directory:
                producer=Path(directory)/'producer';producer.mkdir();output=Path(directory)/'independent'
                bad=deepcopy(base)
                if field=='authority':bad[field]='UNIFORM_THEOREM'
                else:bad['cases'][0]['source_kind']='MODIFIED_Q2_NOT_ZETA'
                (producer/'result.json').write_text(json.dumps(bad),encoding='utf8')
                with patch.object(R,'evaluate_case',side_effect=AssertionError('must reject before reconstruction')):
                    with self.assertRaises(R.B.InvalidRequest):R.verify_campaign(producer,output,require_clean=False)
        bad=deepcopy(self.producer);bad['source_kind']='MODIFIED_Q2_NOT_ZETA'
        with self.assertRaises(R.B.InvalidRequest):R.compare(bad,self.checker)


if __name__=='__main__':unittest.main()
