"""Exact adversaries and bounded actual-source point regressions (no Lean authority)."""
from copy import deepcopy
from fractions import Fraction as F
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(HERE))
import source_backend as B
import source_evaluator as E
import source_checker as C


def mv(A,v):return [sum((a*x for a,x in zip(row,v)),F(0)) for row in A]
def dot(v,w):return sum((a*b for a,b in zip(v,w)),F(0))
def census(root):return {str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest()
                         for p in Path(root).rglob('*') if p.is_file()}


class ExactSourceControls(unittest.TestCase):
    def test_symbolic_seed_cleared_polynomials_independent(self):
        import sympy as sp
        a=sp.symbols('a');n=list(range(-3,4))
        e1=[0,1,-4,6,-4,1,0];e2=[1,0,-9,16,-9,0,1]
        u=[6*(a+4)*x-(a+9)*y for x,y in zip(e1,e2)]
        self.assertEqual(u,u[::-1])
        for k in (0,1,2):self.assertEqual(sp.expand(sum(t**k*x for t,x in zip(n,u))),0)
        denominator=sp.prod(a+t*t for t in n)
        for k in (0,2):
            self.assertEqual(sp.cancel(denominator*sum(t**k*x/(a+t*t) for t,x in zip(n,u))),0)
        self.assertEqual(sp.expand(sum(x*x for x in u)),84*(11*a*a+18*a+21).expand())
        self.assertEqual(sp.expand(sum(t*t*x*x for t,x in zip(n,u))),36*(21*a*a+98*a+181).expand())
        self.assertEqual(sp.expand(sum(t**4*x for t,x in zip(n,u))),-720)
        self.assertEqual(B.symbolic_seed_checks()['M4'],-720)

    def test_exact_legal_projectors_and_dimensions(self):
        for K in (2,3):
            n,q,P,Q=B.rational_projectors(K);N=len(n)
            for A,parity in ((P,1),(Q,-1)):
                self.assertEqual(sum(A[i][i] for i in range(N)),K-1)
                for j in range(N):
                    v=[A[i][j] for i in range(N)]
                    self.assertEqual(mv(A,v),v)
                    self.assertEqual(v,[parity*x for x in v[::-1]])
                    for k in (0,1,2):self.assertEqual(sum(t**k*x for t,x in zip(n,v)),0)
            self.assertEqual([mv(P,[Q[i][j] for i in range(N)]) for j in range(N)],[[0]*N]*N)
            self.assertGreater(dot(q,q),0)

    def test_regular_resonant_and_cutoff_tie_toys_are_not_actual_source(self):
        A,b,d=F(1),F(2),F(3)
        w=[-b/A,F(1)];T=[[A,b],[b,d]]
        self.assertEqual(dot(w,mv(T,w)),d-b*b/A)
        self.assertLess(dot(w,mv(T,w)),0)
        # Exact resonant branch: shell alone has zero energy, full witness −1.
        T=[[F(0),F(1)],[F(1),F(0)]];w=[F(-1,2),F(1)]
        self.assertEqual(dot(w,mv(T,w)),-1)
        self.assertEqual(dot(w,w),F(5,4))
        self.assertEqual(T[1][1],0)
        # Equal first discrete cutoffs do not identify spectral bottom values.
        even=[F(1),F(-1)];odd=[F(2),F(-3)]
        self.assertEqual(next(i for i,x in enumerate(even) if x<0),next(i for i,x in enumerate(odd) if x<0))
        self.assertNotEqual(even[-1],odd[-1])

    def test_same_newborn_geometry_source_alone_kernel_counterexample(self):
        # Synthetic exact rational model; no claim that these matrices are ζ.
        J=[F(4,5),F(3,5)];e=[F(-3,5),F(4,5)]
        Te=[[F(1),F(1)],[F(1),F(-1)]];To=[[F(0),F(0)],[F(0),F(-2)]]
        source=[[To[i][j]-Te[i][j] for j in range(2)] for i in range(2)]
        self.assertEqual(dot(J,J),1);self.assertEqual(dot(e,e),1);self.assertEqual(dot(J,e),0)
        A,b,d=dot(J,mv(Te,J)),dot(J,mv(Te,e)),dot(e,mv(Te,e))
        self.assertEqual((A,b,d),(F(31,25),F(-17,25),F(-31,25)))
        w=[x-y*b/A for x,y in zip(e,J)]
        self.assertEqual(w,[F(-5,31),F(35,31)])
        self.assertEqual(dot(w,mv(Te,w)),F(-50,31))
        self.assertEqual(source,[[-1,-1],[-1,-1]])
        Fw=mv(source,w);Tw=mv(Te,w);whole=[x+y for x,y in zip(Fw,Tw)]
        self.assertEqual(Fw,[F(-30,31),F(-30,31)])
        self.assertEqual(whole,[F(0),F(-70,31)])
        self.assertEqual(whole,mv(To,w))
        self.assertEqual(whole[0],0);self.assertNotEqual(Fw[0],0)
        self.assertEqual(dot(J,mv(To,J)),F(-18,25))

    def test_all_prime_powers_including_nonprimes(self):
        self.assertEqual(B.prime_powers(9),[(2,2,1),(3,3,1),(4,2,2),(5,5,1),(7,7,1),(8,2,3),(9,3,2)])
        self.assertNotIn(6,[row[0] for row in B.prime_powers(64)])
        self.assertIn((64,2,6),B.prime_powers(64))


class FailClosedInputs(unittest.TestCase):
    def test_request_budget_and_unknown_fields(self):
        case=deepcopy(E.EXPECTED_CASES[0])
        mutations=[{'K':True},{'K':4},{'Q':True},{'Q':65},{'extra':0},
                   {'aperture':{'kind':'rational','value':'0'}},
                   {'aperture':{'kind':'rational','value':'2/2'}},
                   {'aperture':{'kind':'ball','value':'1/2','epsilon':'1/100'}}]
        for change in mutations:
            with self.subTest(change=change),self.assertRaises(B.InvalidRequest):B.validate_request({**case,**change})

    def test_seam_requires_exact_constructor_and_matching_floor(self):
        for Q,n in ((1,2),(2,True),(64,64)):
            with self.subTest(Q=Q,n=n),self.assertRaises(B.InvalidRequest):
                B.validate_request({'id':'bad','K':3,'Q':Q,'aperture':{'kind':'log_integer','n':n}})

    def test_input180_endpoint4096_budgets_remain_separate(self):
        value=str(F(1,2**700))
        self.assertGreater(len(value),180)
        self.assertEqual(B.endpoint(value),F(1,2**700))
        with self.assertRaises(B.InvalidRequest):B.rational(value)
        with self.assertRaises(B.InvalidRequest):B.endpoint('1/'+('9'*4096))
        with self.assertRaises(B.InvalidRequest):C.interval({'lower':'2/2','upper':'2'})

    def test_strict_json_duplicates_floats_and_resources(self):
        for raw in (b'{"x":1,"x":2}',b'{"x":1.0}',b'{"x":NaN}',b'\xff',b'['*70+b'0'+b']'*70):
            with self.subTest(raw=raw[:32]),self.assertRaises(B.InvalidRequest):B.strict_json(raw)
        with self.assertRaises(B.InvalidRequest):B.strict_json(b'{}',1)

    def test_valid_wrong_cell_is_unresolved_not_invalid(self):
        case=deepcopy(E.EXPECTED_CASES[0]);case['Q']=2
        B.validate_request(case)
        with self.assertRaisesRegex(B.Unresolved,'AMBIGUOUS_OR_WRONG_PRIME_FLOOR'):B.evaluate_request(case)

    def test_nonfinite_quadrature_cannot_certify_a_valid_request(self):
        from flint import acb
        canonical=B.load_local('_opica3_canonical_source_arb',B.ROUTE/'canonical_source_arb.py')
        with patch.object(canonical,'_regularized_arch_scale',return_value=acb('nan')):
            with self.assertRaisesRegex(B.Unresolved,'QUADRATURE_RESOURCE_OR_NONFINITE_BOUND'):
                B.evaluate_request(E.EXPECTED_CASES[0])

    def test_zero_pole_normal_denominator_is_unresolved(self):
        n,q,E0,O0=B.rational_projectors(2)
        broken=(n,q,[[F(0)]*5 for _ in range(5)],O0)
        with patch.object(B,'rational_projectors',return_value=broken):
            with self.assertRaisesRegex(B.Unresolved,'POLE_NORMAL_DENOMINATOR_UNRESOLVED'):
                B.evaluate_request(E.EXPECTED_CASES[0])

    def test_no_kernel_from_zero_containment_and_no_claim_upgrade(self):
        with self.assertRaises(B.InvalidRequest):C.interval({'lower':'-1','upper':'1'})
        box={'lower':str(F(-1,2**80)),'upper':str(F(1,2**80))}
        self.assertLessEqual(C.interval(box)[0],0);self.assertGreaterEqual(C.interval(box)[1],0)
        for key in B.CAPS:
            doc={'authority':'FINITE_INTERVAL_EVIDENCE_ONLY','is_zero_generated_detector':False,**B.CAPS}
            doc[key]=True
            with self.subTest(key=key),self.assertRaises(B.InvalidRequest):C.caps(doc)

    def test_type_sensitive_exact_fields(self):
        self.assertFalse(B.identical({'Q':1},{'Q':True}))
        self.assertFalse(B.identical({'unaccounted_prime_terms':0},{'unaccounted_prime_terms':False}))
        self.assertFalse(B.identical([1],[True]))

    def test_public_producer_deadline_is_unresolved(self):
        with tempfile.TemporaryDirectory(prefix='opica3-deadline-') as tmp:
            identity={'head':'a'*40,'tree':'b'*40,'clean':True,'source_sha256':{}}
            with patch.object(B,'source_identity',return_value=identity),patch.object(E.subprocess,'run',side_effect=subprocess.TimeoutExpired('unit-fixture',1)) as run:
                # Mocked source identity must not inherit CI's real requested head.
                with patch.dict(os.environ,{'REQUESTED_HEAD':'c'*40}):
                    with self.assertRaisesRegex(B.InvalidRequest,'Another requested head'):
                        E.evaluate(E.CASES,Path(tmp)/'wrong-head',128,1)
                run.assert_not_called()
                self.assertFalse((Path(tmp)/'wrong-head').exists())
                with patch.dict(os.environ,{'REQUESTED_HEAD':identity['head']}):
                    result=E.evaluate(E.CASES,Path(tmp)/'result',128,1)
            self.assertEqual(result['status'],'UNRESOLVED')
            self.assertEqual(len(result['cases']),3)
            for row in result['cases']:
                self.assertTrue(row['command']['timeout']);self.assertIsNone(row['command']['returncode'])
                self.assertEqual(B.strict_json((Path(tmp)/'result'/row['file']).read_bytes())['reason'],'WORKER_WALL_DEADLINE')

    def test_checker_deadline_is_unresolved(self):
        with tempfile.TemporaryDirectory(prefix='opica3-check-deadline-') as tmp:
            with patch.object(C.subprocess,'run',side_effect=subprocess.TimeoutExpired('unit-fixture',30)):
                with self.assertRaisesRegex(B.Unresolved,'INDEPENDENT_CHECKER_WALL_DEADLINE'):
                    C.recompute_case(E.EXPECTED_CASES[0],256,Path(tmp))

    def test_checkout_or_artifact_overwrite_is_refused(self):
        with self.assertRaises(B.InvalidRequest):E.external(HERE/'forbidden')
        with tempfile.TemporaryDirectory(prefix='opica3-overwrite-') as tmp:
            with self.assertRaises(B.InvalidRequest):E.evaluate(E.CASES,Path(tmp),128,30)


class ActualSourceEnclosures(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp=tempfile.TemporaryDirectory(prefix='opica3-actual-finite-')
        cls.addClassCleanup(cls.temp.cleanup)
        cls.directory=Path(cls.temp.name);cls.cases=E.prescribed_cases();cls.unit={};cls.direct={}
        for case in cls.cases:
            for mode,bits,dest in (('unit',128,cls.unit),('direct',256,cls.direct)):
                folder=cls.directory/(case['id']+'-'+mode);folder.mkdir()
                if mode=='direct':dest[case['id']]=C.recompute_case(case,bits,folder)
                else:
                    output=folder/(case['id']+'.json')
                    argv=[sys.executable,*(['-O'] if sys.flags.optimize else []),'-B',str(HERE/'source_evaluator.py'),
                          '--_worker',case['id'],'--precision-bits',str(bits),'--worker-output',str(output)]
                    result=subprocess.run(argv,cwd=B.REPO,capture_output=True,timeout=30,check=False)
                    if result.returncode!=0:raise RuntimeError('Actual unit worker failed: '+result.stderr.decode('utf-8',errors='replace'))
                    dest[case['id']]=B.strict_json(output.read_bytes())

    def test_all_three_actual_cases_direct_containment_and_hermiticity(self):
        for case in self.cases:
            with self.subTest(case=case['id']):
                count=C.compare_case(self.unit[case['id']],self.direct[case['id']],case,128)
                self.assertGreater(count,150)

    def test_k2_empty_native_carrier_has_no_fake_eigenvalue(self):
        doc=self.unit['K2_Q1_HALF']
        for parity in ('even','odd'):
            self.assertEqual(doc['enclosures']['neutral'][parity]['dimension'],0)
            self.assertIsNone(doc['enclosures']['neutral'][parity]['rayleigh_bottom'])
        self.assertEqual(doc['enclosures']['source_correction']['status'],'NOT_APPLICABLE_EMPTY_NEUTRAL_CARRIER')

    def test_q4_actual_entry_includes_weight_and_diagonal_factor_two(self):
        from flint import arb,ctx,fmpq
        doc=self.unit['K3_Q4_THREE_HALVES'];effect=doc['enclosures']['prime_power_4_effect']
        self.assertEqual([(r['q'],r['prime'],r['exponent']) for r in doc['enclosures']['prime_power_atoms']],
                         [(2,2,1),(3,3,1),(4,2,2)])
        old=ctx.prec;ctx.prec=256
        try:
            L=arb(fmpq(3,2));C0=B.load_local('_opica3_canonical_source_arb',B.ROUTE/'canonical_source_arb.py')
            missing=sum((arb(p).log()/arb(q).sqrt()*C0.q_basis(0,0,arb(q).log(),L) for q,p in ((2,2),(3,3))),arb(0))
            q4=arb(2).log()/2*C0.q_basis(0,0,arb(4).log(),L)
            full=missing+q4
            lower,upper=C.interval(doc['enclosures']['components']['prime_power'][3][3])
            self.assertTrue(full>arb(fmpq(lower.numerator,lower.denominator)))
            self.assertTrue(full<arb(fmpq(upper.numerator,upper.denominator)))
            lo,hi=C.interval(effect['full_00_minus_missing_4_00'])
            self.assertLess(hi,0)
            self.assertTrue(-q4>arb(fmpq(lo.numerator,lo.denominator)))
            self.assertTrue(-q4<arb(fmpq(hi.numerator,hi.denominator)))
            self.assertTrue(missing<arb(fmpq(lower.numerator,lower.denominator)))
        finally:ctx.prec=old

    def test_symbolic_log2_seam_is_not_a_float_floor_or_omitted_tail(self):
        doc=self.unit['K3_LOG2_SEAM']
        self.assertEqual(doc['cutoff'],{'mode':'EXACT_SYMBOLIC_LOG_POINT','active_Q':2,'summed_through':1,
             'whole_input_ball_in_cell':False,'entering_atom':'EXACT_ZERO_BY_qBasis_aperture_eq_zero'})
        self.assertEqual(doc['enclosures']['prime_power_atoms'],[])
        self.assertEqual(doc['budgets']['unaccounted_prime_terms'],0)

    def test_raw_and_projected_output_residuals_are_both_retained(self):
        doc=self.unit['K3_Q4_THREE_HALVES'];c=doc['enclosures']['source_correction']
        self.assertIn('raw_index_output_residual',c);self.assertIn('projected_odd_output_residual',c)
        self.assertNotEqual(c['raw_index_output_residual'],c['projected_odd_output_residual'])
        C.consistency(doc)

    def test_narrowed_intersecting_or_changed_source_enclosures_rejected(self):
        case=self.cases[1];good=self.unit[case['id']];refined=self.direct[case['id']]
        bad=deepcopy(good);box=bad['enclosures']['matrix_real'][0][0]
        lo,hi=C.interval(box);box['lower']=str((lo+hi)/2);box['upper']=box['lower']
        with self.assertRaises(B.InvalidRequest):C.compare_case(bad,refined,case,128)
        for field in ('raw_index_output_residual','projected_odd_output_residual'):
            bad=deepcopy(good);bad['enclosures']['source_correction'].pop(field)
            with self.subTest(field=field),self.assertRaises(B.InvalidRequest):C.compare_case(bad,refined,case,128)
        bad=deepcopy(good);bad['enclosures']['prime_power_atoms'].pop()
        with self.assertRaises(B.InvalidRequest):C.compare_case(bad,refined,case,128)

    def test_boolean_replacements_and_uncertified_sign_rejected(self):
        case=self.cases[0];good=self.unit[case['id']];refined=self.direct[case['id']]
        for path in (('request','Q'),('cutoff','active_Q'),('budgets','unaccounted_prime_terms')):
            bad=deepcopy(good);bad[path[0]][path[1]]=False if path[1]=='unaccounted_prime_terms' else True
            with self.subTest(path=path),self.assertRaises(B.InvalidRequest):C.compare_case(bad,refined,case,128)
        case=self.cases[1];bad=deepcopy(self.unit[case['id']]);bad['enclosures']['neutral']['even']['sign']='STRICT_NEGATIVE'
        with self.assertRaises(B.InvalidRequest):C.compare_case(bad,self.direct[case['id']],case,128)

    def test_actual_512_bit_producer_remains_finite(self):
        folder=self.directory/'actual512';folder.mkdir();case=self.cases[1];output=folder/(case['id']+'.json')
        result=subprocess.run([sys.executable,*(['-O'] if sys.flags.optimize else []),'-B',str(HERE/'source_evaluator.py'),'--_worker',case['id'],
                               '--precision-bits','512','--worker-output',str(output)],capture_output=True,timeout=30,check=False)
        self.assertEqual(result.returncode,0,result.stderr.decode('utf-8',errors='replace'))
        doc=B.strict_json(output.read_bytes());self.assertEqual(doc['status'],'FINITE_ENCLOSURES')
        self.assertEqual(doc['precision_bits'],512)
        self.assertGreater(C.compare_enclosures(doc['enclosures'],self.direct[case['id']]['enclosures']),150)

    def test_successful_checker_leaves_entire_input_inventory_unchanged(self):
        # Synthetic provenance wrapper for a unit test, around actual computed
        # matrices. This does not create a current-head evidence claim.
        collection=self.directory/'input-artifacts';root=collection/'evaluator';root.mkdir(parents=True)
        identity={'head':'a'*40,'tree':'b'*40,'clean':True,'source_sha256':{}}
        for mode in ('normal','optimized'):
            directory=root/'source-evaluator'/mode;directory.mkdir(parents=True);rows=[]
            for case in self.cases:
                name=case['id'];file=directory/(name+'.json');file.write_text(json.dumps(self.unit[name]))
                out=directory/(name+'.stdout.log');err=directory/(name+'.stderr.log')
                out.write_text(json.dumps({'case':name,'status':'FINITE_ENCLOSURES'}));err.write_bytes(b'')
                argv=[sys.executable,*(['-O'] if mode=='optimized' else []),'-B',str(HERE/'source_evaluator.py'),
                      '--_worker',name,'--precision-bits','128','--worker-output',str(file)]
                rows.append({'id':name,'request':case,'outcome':'FINITE_ENCLOSURES','file':file.name,'sha256':B.digest(file),
                    'command':{'argv':argv,'returncode':0,'timeout':False,'elapsed_ms':0,'stdout':out.name,'stderr':err.name,
                               'stdout_sha256':B.digest(out),'stderr_sha256':B.digest(err)}})
            report={'schema':'OPICA3_FINITE_SOURCE_EVALUATOR_V1','status':'PASS_FINITE_SOURCE_ENCLOSURES',
                'checked_commit':identity['head'],'checked_tree':identity['tree'],'source_identity':identity,
                'backend_version':'0.9.0','python_optimized':mode=='optimized','precision_bits':128,'seconds_per_case':30,
                'case_manifest_sha256':B.digest(E.CASES),'cases':rows,'authority':'FINITE_INTERVAL_EVIDENCE_ONLY',
                'is_zero_generated_detector':False,**B.CAPS}
            (directory/'result.json').write_text(json.dumps(report))
        before=census(collection)
        with patch.object(B,'source_identity',return_value=identity):
            result=C.verify_evaluator_evidence(B.REPO,root,identity['head'],identity['tree'],True,
                                                recompute_output=self.directory/'retained-direct-check',
                                                artifact_collection_root=collection)
        self.assertEqual(result['status'],C.PASS_STATUS)
        self.assertEqual(result['independently_recomputed_cases'],3)
        self.assertEqual(census(collection),before)
        self.assertGreater(result['contained_interval_comparisons'],900)
        with patch.object(B,'source_identity',return_value=identity):
            with self.assertRaises(B.InvalidRequest):
                C.verify_evaluator_evidence(B.REPO,root,identity['head'],identity['tree'],True,
                                            recompute_output=collection/'bad',artifact_collection_root=collection)
        self.assertEqual(census(collection),before)


if __name__=='__main__':unittest.main()
