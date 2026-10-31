"""Real 256/512-bit complete source and independent-geometry adversaries."""
from copy import deepcopy
from fractions import Fraction as F
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE=Path(__file__).resolve().parents[1]
def module(name,path):
    if name in sys.modules:return sys.modules[name]
    s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m
E=module('_opica4_source_evaluator',HERE/'source_evaluator.py');B=E.B
C=module('_opica4_source_checker',HERE/'source_checker.py')


class ExactGeometry(unittest.TestCase):
    def test_all_polynomial_basis_constraints_and_full_rank_exact(self):
        import sympy as sp
        a=sp.symbols('a',positive=True)
        for K in (4,5):
            cols=[[sp.Rational(c.numerator,c.denominator)+sp.Rational(l.numerator,l.denominator)*a for c,l in v] for v in B.exact_basis_coefficients(K)]
            ns=list(range(-K,K+1));Te=sp.Matrix(cols).T;To=sp.diag(*ns)*Te
            self.assertEqual(Te.rank(),K-2);self.assertEqual(To.rank(),K-2)
            for v in cols:
                self.assertEqual(v,v[::-1])
                for k in (0,1,2):self.assertEqual(sp.expand(sum(n**k*x for n,x in zip(ns,v))),0)
                self.assertEqual(sp.cancel(sum(x/(a+n*n) for n,x in zip(ns,v))),0)
                self.assertEqual(sp.cancel(sum(n*n*x/(a+n*n) for n,x in zip(ns,v))),0)
            self.assertNotEqual(Te.T*Te,To.T*To)

    def test_repeated_eigenspace_grouped_projector_and_defect_rejection(self):
        groups=B.exact_grouped_projectors([[2,0,0],[0,2,0],[0,0,3]])
        self.assertEqual([x['multiplicity'] for x in groups],[2,1])
        self.assertEqual(groups[0]['projector'],[['1','0','0'],['0','1','0'],['0','0','0']])
        grouped=B.exact_grouped_projectors([[2,0,0],[0,2,0],[0,0,3]],source_row=[1,2,3],source_vector=[4,5,6])
        self.assertEqual([x['residue'] for x in grouped],['14','18'])
        with self.assertRaises(B.Unresolved):B.exact_grouped_projectors([[2,1],[0,2]])

    def test_small_z_correct_coefficient_and_exact_projectors(self):
        import sympy as sp
        z=sp.symbols('z');self.assertEqual(sp.series(sp.exp(z/2)*z/(2*sp.sinh(z)),z,0,4).removeO(),sp.Rational(1,2)+z/4-z*z/48-z**3/32)
        for K in (4,5):
            n,q,e,o=B.R3.rational_projectors(K)
            self.assertTrue(all(type(x)is F for row in o for x in row))
            self.assertEqual(sum(o[i][i] for i in range(2*K+1)),K-1)
            self.assertEqual(sum(e[i][i] for i in range(2*K+1)),K-1)


class FiniteSource(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cases=E.prescribed_cases();cls.unit={};cls.direct={}
        # These are actual native validated integrations, never mocked responses.
        for case in cls.cases:
            cls.unit[case['id']]=B.evaluate_request(case,256,'unit',80)
            cls.direct[case['id']]=B.evaluate_request(case,512,'direct',112)

    def test_all_six_independent_physical_metric_and_projector_replays(self):
        for case in self.cases:
            with self.subTest(case=case['id']):
                self.assertGreater(C.compare_case(self.unit[case['id']],self.direct[case['id']],case,256),600)

    def test_required_finite_scientific_dispositions(self):
        for v in self.unit.values():C.disposition(v)
        k5=self.unit['K5_Q5_SEVEN_FOURTHS']['enclosures']['spectrum']
        self.assertGreater(C.interval(k5['positive_reciprocal_mass'])[0],1)
        self.assertLess(C.interval(k5['signed_response_at_zero'])[1],1)
        for name in ('K4_Q2_ENTERING_Q2','K4_Q4_ENTERING_Q4'):
            for p in self.unit[name]['enclosures']['entering_atom_control']['parities'].values():self.assertLess(C.interval(p['determinant'])[1],0)

    def test_missing_q4_wrong_metric_omitted_correction_and_double_contamination_rejected(self):
        case=self.cases[1];good=self.unit[case['id']];refined=self.direct[case['id']]
        bad=deepcopy(good);bad['enclosures']['prime_power_atoms']=[a for a in bad['enclosures']['prime_power_atoms'] if a['q']!=4]
        mutations=[bad]
        bad=deepcopy(good);bad['enclosures']['transfer']['codomain_metric']=bad['enclosures']['transfer']['domain_metric'];mutations.append(bad)
        bad=deepcopy(good);del bad['enclosures']['correction']['removed_output_coefficient'];mutations.append(bad)
        bad=deepcopy(good);bad['enclosures']['correction']['corrected_source_row']=bad['enclosures']['correction']['source_moment'];mutations.append(bad)
        bad=deepcopy(good);x=bad['enclosures']['matrix_real'][0][0];x['lower']=x['upper']=str(F(float(F(x['lower']))));mutations.append(bad)
        bad=deepcopy(good);bad['enclosures']['spectrum']['groups'][0]['multiplicity']=True;mutations.append(bad)
        for bad in mutations:
            with self.assertRaises(B.InvalidRequest):C.compare_case(bad,refined,case,256)

    def test_source_seam_and_output_residual_identity_adversaries(self):
        for case in self.cases:
            good=self.unit[case['id']];refined=self.direct[case['id']]
            bad=deepcopy(good);bad['source']['kind']='VON_MANGOLDT' if case['source']['kind']!='VON_MANGOLDT' else 'MODIFIED_Q2_NOT_ZETA'
            with self.assertRaises(B.InvalidRequest):C.compare_case(bad,refined,case,256)
            bad=deepcopy(good);bad['enclosures']['correction'].pop('projected_odd_output_residual')
            with self.assertRaises(B.InvalidRequest):C.compare_case(bad,refined,case,256)

    def test_zero_contains_never_grants_kernel_or_residue_authority(self):
        case=self.cases[0];bad=deepcopy(self.unit[case['id']]);tiny={'lower':str(F(-1,2**80)),'upper':str(F(1,2**80))}
        bad['enclosures']['physical']['even']['eigenvalues'][0]=tiny
        with self.assertRaisesRegex(B.InvalidRequest,'Near zero'):C.disposition(bad)
        self.assertFalse(bad['is_zero_generated_detector']);self.assertEqual(bad['RH'],'OPEN')


class FailClosed(unittest.TestCase):
    def test_wrong_cells_nonfinite_source_and_singular_gram_unresolved(self):
        case=deepcopy(E.prescribed_cases()[0]);case['Q']=4
        with self.assertRaisesRegex(B.Unresolved,'PRIME_FLOOR'):B.evaluate_request(case)
        case=E.prescribed_cases()[0];canonical=B.R3.load_local('_opica3_canonical_source_arb',B.R3.ROUTE/'canonical_source_arb.py')
        from flint import acb
        with patch.object(canonical,'_regularized_arch_scale',return_value=acb('nan')):
            with self.assertRaisesRegex(B.Unresolved,'QUADRATURE'):B.evaluate_request(case)
        with patch.object(B,'exact_basis_coefficients',return_value=[[(F(0),F(0))]*9]*2):
            with self.assertRaisesRegex(B.Unresolved,'GRAM'):B.evaluate_request(case)

    def test_production_has_no_assert_and_closed_inputs(self):
        import ast
        for name in ('source_backend.py','source_evaluator.py','source_checker.py'):
            self.assertFalse(any(isinstance(x,ast.Assert) for x in ast.walk(ast.parse((HERE/name).read_text()))))
        case=E.prescribed_cases()[0]
        for change in ({'K':True},{'Q':True},{'extra':0},{'source':{'kind':'VON_MANGOLDT','prime2_multiplier':'1/2'}},{'aperture':{'kind':'rational','value':'2/2'}}):
            with self.assertRaises(B.InvalidRequest):B.validate_request({**case,**change})

    def test_manifest_cannot_rebind_same_case_id_to_another_point(self):
        doc=B.strict_json(E.CASES.read_bytes());doc['cases'][0]['aperture']['value']='3/2'
        with patch.object(E.B,'strict_json',return_value=doc):
            with self.assertRaisesRegex(B.InvalidRequest,'prescribed mathematical input'):E.prescribed_cases()

    def test_direct_checker_does_not_call_producer_basis_constructor(self):
        with patch.object(B,'exact_basis_coefficients',side_effect=RuntimeError('producer basis unavailable')):
            value=B.evaluate_request(E.prescribed_cases()[0],512,'direct',112)
        self.assertEqual(value['status'],'FINITE_ENCLOSURES')

    def test_exported_zero_or_cluster_is_unresolved_before_inertia(self):
        with self.assertRaisesRegex(B.Unresolved,'NEAR_ZERO'):B.require_exported_spectrum([{'lower':'-1/100','upper':'1/100'}])
        with self.assertRaisesRegex(B.Unresolved,'CLUSTER'):B.require_exported_spectrum([{'lower':'1','upper':'2'},{'lower':'3/2','upper':'3'}])
        B.require_exported_spectrum([{'lower':'-2','upper':'-1'},{'lower':'1','upper':'2'}])

    def test_recorded_execution_root_survives_artifact_relocation(self):
        self.assertEqual(str(B.recorded_root('/tmp/original/source/normal')),'/tmp/original/source/normal')
        self.assertEqual(str(B.recorded_root('C:\\native\\source\\normal')),'C:\\native\\source\\normal')
        for root in ('relative/root','/tmp/../source','/tmp/source/'):
            with self.assertRaises(B.InvalidRequest):B.recorded_root(root)

    def test_interpreter_alias_uses_canonical_worker_receipts_in_both_modes(self):
        canonical=E.python_executable()
        alias=str(Path(canonical).parent)+os.sep+'.'+os.sep+Path(canonical).name
        cases=E.prescribed_cases()
        with tempfile.TemporaryDirectory(dir=B.REPO.parent) as tmp:
            output=Path(tmp)/'producer'
            with patch.object(sys,'executable',alias):
                result=E.lane(output,require_clean=False)
                self.assertEqual(result['independently_recomputed_cases'],len(cases))
                for mode in ('normal','optimized'):
                    path=output/mode/'result.json';doc=B.strict_json(path.read_bytes())
                    self.assertEqual(doc['runtime']['python_executable'],canonical)
                    self.assertEqual(doc['cases'][0]['command']['argv'][0],canonical)
                # Even another spelling of the same executable cannot replace
                # the exact canonical command after its receipt was produced.
                doc['cases'][0]['command']['argv'][0]=alias
                path.write_text(json.dumps(doc),encoding='utf-8')
                with self.assertRaisesRegex(B.InvalidRequest,'Wrong bound worker command'):
                    C.verify_evaluator_evidence(output,Path(tmp)/'must-not-recompute',require_clean=False)
                self.assertFalse((Path(tmp)/'must-not-recompute').exists())

    def test_modified_entering_q2_atom_uses_same_source_weight(self):
        case=deepcopy(E.prescribed_cases()[4]);original=B.evaluate_request(case,256)
        case['source']={'kind':'MODIFIED_Q2_NOT_ZETA','prime2_multiplier':'1/2'}
        modified=B.evaluate_request(case,256)
        for parity in ('even','odd'):
            a=C.interval(original['enclosures']['entering_atom_control']['parities'][parity]['determinant'])
            b=C.interval(modified['enclosures']['entering_atom_control']['parities'][parity]['determinant'])
            self.assertLessEqual(b[0],a[1]/4);self.assertGreaterEqual(b[1],a[0]/4)

    def test_missing_execution_and_claim_upgrade_rejected(self):
        case=E.prescribed_cases()[0]
        with self.assertRaisesRegex(B.InvalidRequest,'execution identity'):C.execution({},B.source_identity(),case,256)
        for k in B.CAPS:
            doc={'authority':'FINITE_INTERVAL_EVIDENCE_ONLY','is_zero_generated_detector':False,**B.CAPS};doc[k]=True
            with self.assertRaises(B.InvalidRequest):C.caps(doc)

    def test_worker_timeout_and_evidence_path_rejected(self):
        with tempfile.TemporaryDirectory(dir=B.REPO.parent) as tmp:
            with patch.object(C.subprocess,'run',side_effect=subprocess.TimeoutExpired('test',60)):
                with self.assertRaisesRegex(B.Unresolved,'DEADLINE'):C.recompute_case(E.prescribed_cases()[0],512,Path(tmp))
        with self.assertRaises(B.InvalidRequest):E.external(HERE/'evidence')


if __name__=='__main__':unittest.main()
