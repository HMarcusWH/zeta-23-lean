import unittest
from research.RHRC.integration.opica_integrated_epoch.admission import verify_delta,SEAL,VALIDATOR
from research.RHRC.integration.opica_integrated_epoch.release import verify_canonical

class IntegratedAdmissionTests(unittest.TestCase):
    def test_closed_delta(self):
        x=("100644","blob","a"*40);y=("100644","blob","b"*40)
        baseline={"frozen":x,"generated":x,"edit":x}
        current={**baseline,"generated":y,"edit":y,SEAL:x,VALIDATOR:y}
        args=({"reviewed":{"edit":"b"*40}},"a"*40,"b"*40,{"generated"})
        self.assertEqual(verify_delta(baseline,current,*args),["generated"])
        for bad in ({**current,"frozen":y},{**current,"new":x},{k:v for k,v in current.items() if k!="frozen"},{**current,"edit":x}):
            with self.assertRaises(Exception):verify_delta(baseline,bad,*args)
    def test_canonical_bytes(self):
        before={"x":"a"};after={"x":"b"}
        r={"status":"REVIEW_ONLY_GENERATED_STATE","source_head":"h","source_tree":"t","RH":"OPEN","C1":"OPEN","Step4":"OPEN","proof_acceptance":False,"total_count":81,"active_count":77,"frozen_count":4,"before_sha256":before,"after_write_sha256":after,"after_check_sha256":after,"changed_paths":["x"],"changed_count":1}
        verify_canonical(r,"h","t",before,after,{"x"})
        for changed in ({**r,"after_check_sha256":before},{**r,"proof_acceptance":True},{**r,"changed_paths":[]}):
            with self.assertRaises(Exception):verify_canonical(changed,"h","t",before,after,{"x"})

if __name__=="__main__":unittest.main()
