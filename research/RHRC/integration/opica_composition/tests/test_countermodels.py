import unittest
from research.RHRC.integration.opica_composition.countermodels import run_countermodel_bank

class CountermodelTests(unittest.TestCase):
    def test_exact_rankone_controls_are_source_scoped(self):
        rows=run_countermodel_bank()
        self.assertEqual(len(rows),len({r['id'] for r in rows}))
        self.assertTrue(all(r['source_kind']=='SYNTHETIC_CONTROL' and r['actual_zeta_counterexample'] is False for r in rows))
        shared=next(r for r in rows if r['id']=='SHARED_INVISIBLE_NEGATIVE_GROUND')
        self.assertEqual(shared['common_negative_ground'],'-1')
        self.assertEqual(shared['own_predecessors'],{'A':'2>0','B':'3>0'})
    def test_resonant_cost_preserves_nonunit_w(self):
        row=next(r for r in run_countermodel_bank() if r['id']=='NONUNIT_RESONANT_COST')
        self.assertEqual(row['witness_norm_sq'],'2501');self.assertEqual(row['normalized_energy'],'-1/2501')

if __name__=='__main__':unittest.main()
