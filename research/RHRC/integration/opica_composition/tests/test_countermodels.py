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
    def test_pick_index_and_physical_index_are_not_identified(self):
        row=next(r for r in run_countermodel_bank() if r['id']=='RANKONE_FIVE_NEGATIVE_PICK_SQUARES')
        self.assertEqual(row['negative_squares'],5)
        self.assertIn('positive_A',row['preserved_premises'])
        self.assertEqual(row['evaluation_determinant'],'1296*I/53125')
    def test_repeated_spectral_coordinates_are_grouped(self):
        row=next(r for r in run_countermodel_bank() if r['id']=='GROUPED_REAL_COORDINATES_COMPLEX')
        self.assertEqual(row['grouped_residue'],'1')
        self.assertTrue(all('I' in c for c in row['coordinate_residues']))
    def test_overlap_and_visibility_controls_preserve_scope(self):
        rows={r['id']:r for r in run_countermodel_bank()}
        self.assertEqual(rows['CONCENTRATION_OVERLAP_MULTIPLICITY']['source_square_quadratic_lower_bound'],'9/4')
        self.assertEqual(rows['HERGLOTZ_INVISIBLE_NEGATIVE_GROUND']['shared_invisible_ground'],'-1')
        self.assertFalse(rows['HERGLOTZ_INVISIBLE_NEGATIVE_GROUND']['observation_is_native_corrected_source'])
    def test_odd_input_and_instantaneous_kernel_controls(self):
        rows={r['id']:r for r in run_countermodel_bank()}
        odd=rows['ODD_RECIPROCAL_INPUT_DISTINCT']
        self.assertEqual(odd['odd_response'],'-2/3')
        self.assertEqual(odd['wrong_riesz_response'],'-4/3')
        self.assertFalse(rows['INSTANTANEOUS_KERNEL_NOT_INVARIANT']['u_is_eigenmode'])
        self.assertEqual(rows['POSITIVE_MEASURE_NEGATIVE_SUPPORT']['negative_atom_mass'],'1')

if __name__=='__main__':unittest.main()
