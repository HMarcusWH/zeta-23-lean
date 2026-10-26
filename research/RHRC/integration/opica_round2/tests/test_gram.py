from copy import deepcopy
from fractions import Fraction as Q
from pathlib import Path
import sys
import unittest

HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(HERE))
sys.path.insert(0,str(Path(__file__).resolve().parent))
import gram_diagnostics as gram
import native_evaluation as native
from certificate_io import InvalidCertificate,canonical_sha256,parse_complex
from test_native_evaluation import request_fixture


def point(re,im="0"):
    return gram.ComplexInterval(gram.Interval.point(str(re)),gram.Interval.point(str(im)))


def toy_energy(request, *, expected_source):
    """Exact finite Hilbert model tests polarization; this has no native analytic authority."""
    target=parse_complex(request.get("target_coefficient",gram.ONE))
    x=[parse_complex(z) for z in request["coefficients"]]
    def mul(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
    def sub(a,b): return (a[0]-b[0],a[1]-b[1])
    a=(target.re,target.im)
    # Actual model vectors: target=(1+i,3-i); w1=(1,0); w2=(i,1).
    residual=[mul(a,(Q(1),Q(1))),mul(a,(Q(3),Q(-1)))]
    vectors=[[(Q(1),Q(0)),(Q(0),Q(0))],[(Q(0),Q(1)),(Q(1),Q(0))]]
    for c,w in zip(x,vectors):
        for k in range(2): residual[k]=sub(residual[k],mul((c.re,c.im),w[k]))
    energy=sum((re*re+im*im for re,im in residual),Q())
    return {"request_sha256":canonical_sha256(request),"source_identity":dict(expected_source),
            "coefficient_sha256":request["coefficient_sha256"],"lower_square":str(energy),"upper_square":str(energy)}


class GramTests(unittest.TestCase):
    def test_exact_complex_polarization_recovers_b_and_completed_gram(self):
        req=request_fixture()
        req["dictionary_indices"]=["1","2"]
        req["coefficients"]=[gram.ZERO,gram.ZERO]
        original=deepcopy(req)
        out=gram.evaluate_gram(req,expected_source=req["source"],evaluator=toy_energy)
        self.assertEqual(out["q"],{"lower":"12","upper":"12"})
        self.assertEqual(out["b"],[point(1,1).json(),point(4,-2).json()])
        self.assertEqual(out["G"],[[point(1).json(),point(0,1).json()],
                                   [point(0,-1).json(),point(2).json()]])
        self.assertEqual(req,original)
        self.assertFalse(out["asymptotic_claim"])
        self.assertFalse(out["full_release_accepted"])

    def test_primal_energy_uses_conjugation(self):
        q=gram.Interval.point("12")
        b=[point(1,1),point(4,-2)]
        G=[[point(1),point(0,1)],[point(0,-1),point(2)]]
        x=[{"re":"1/3","im":"-1/2"},{"re":"-2","im":"3/4"}]
        req=request_fixture();req.update(coefficients=x,dictionary_indices=["1","2"])
        req["coefficient_sha256"]=native.coefficient_digest(x,req["dictionary_indices"])
        expected=Q(toy_energy(req,expected_source=req["source"])["upper_square"])
        self.assertEqual(gram.primal_interval(q,b,G,x),gram.Interval(expected,expected))

    def test_interval_product_and_square_cross_zero(self):
        a=gram.Interval(Q(-2),Q(3));b=gram.Interval(Q(-4),Q(1))
        self.assertEqual(a*b,gram.Interval(Q(-12),Q(8)))
        self.assertEqual(a.square(),gram.Interval(Q(),Q(9)))

    def test_verified_gershgorin_is_conservative(self):
        G=[[point(3),point(1,1)],[point(1,-1),point(4)]]
        ell=gram.gershgorin_lower(G)
        self.assertGreater(ell,1)
        self.assertLessEqual((3-ell)**2, Q(2)+Q(1,10**20))
        self.assertGreaterEqual((3-ell)**2,Q(2))

    def test_nonhermitian_and_nonreal_diagonal_rejected(self):
        with self.assertRaises(InvalidCertificate): gram.gershgorin_lower([[point(2),point(1)],[point(0),point(2)]])
        with self.assertRaises(InvalidCertificate): gram.gershgorin_lower([[point(2,1)]])

    def test_zero_dimension_has_no_positive_conditioning(self):
        self.assertIsNone(gram.gershgorin_lower([]))
        self.assertEqual(gram.primal_interval(gram.Interval.point("3"),[],[],[]),gram.Interval.point("3"))

    def test_conditioned_gradient_bound_keeps_target(self):
        data={"target":"probeTarget","dictionary":"probeColumn(n): actual completed w shifts",
              "q":gram.Interval.point("2").json(),"b":[point(0).json()],"G":[[point(3).json()]]}
        out=gram.conditioned_gap(data,[gram.ZERO])
        self.assertTrue(out["conditioned"])
        self.assertEqual(out["distance_square_lower"],"2")
        self.assertEqual(out["gradient_square_upper"],"0")
        data["dictionary"]="target v shifts"
        with self.assertRaises(InvalidCertificate): gram.conditioned_gap(data,[gram.ZERO])

    def test_no_unverified_inverse_or_ell(self):
        data={"target":"probeTarget","dictionary":"probeColumn(n): actual completed w shifts",
              "q":gram.Interval.point("2").json(),"b":[point(0).json()],"G":[[point(0).json()]]}
        out=gram.conditioned_gap(data,[gram.ZERO])
        self.assertFalse(out["conditioned"])
        self.assertEqual(out["distance_square_lower"],"0")

    def test_stale_evaluator_and_duplicate_columns_rejected(self):
        req=request_fixture()
        def stale(r,**kw):
            out=toy_energy(r,**kw);out["request_sha256"]="0"*64;return out
        with self.assertRaises(InvalidCertificate): gram.evaluate_gram(req,expected_source=req["source"],evaluator=stale)
        req["dictionary_indices"]=["1","1"]
        with self.assertRaises(InvalidCertificate): gram.evaluate_gram(req,expected_source=req["source"],evaluator=toy_energy)

    def test_exact_sqrt_upper(self):
        upper=gram.sqrt_upper(Q(2),64)
        self.assertGreaterEqual(upper**2,Q(2))
        self.assertLess((upper-Q(1,2**64))**2,Q(2))
        self.assertEqual(gram.sqrt_upper(Q(9),64),Q(3))


if __name__=="__main__": unittest.main()
