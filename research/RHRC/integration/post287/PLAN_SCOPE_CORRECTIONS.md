# Rev4 scope corrections from the PR #290 source review

The pasted plan is a research proposal, not theorem authority. Its original
file remains unchanged. These corrections preserve the distinction between
the candidate law, the witness actually tested and a formal implication.
RH_OPEN.

## The direct functional normalization probe

Rev4 section 14.4 proposed repeating an independent Fourier-side comparison
with an approximated tail in Arb. The implementation instead uses the exact
equivalent digamma representation in physical space. The autocorrelation is
zero beyond L, so the omitted portion is integrated exactly, not approximated.
See `wp2_literature_form_arb_probe.py` and the normalization crosswalk. The
transform's interpretation relative to the external papers is DERIVED; a
finite Arb PASS is not external coercivity or the hard-window domain theorem.

## Two distinct Gamma-window propositions

Rev4 section 15.4 describes a law for every negative shift, while sections
15.2, 15.3 and 15.9 describe a law on the actual selected residual ground.
These are different propositions and must not share one falsification label.

1. **All admissible negative shifts:** the source has the required positive
   aperture and nonnegative odd predecessor, with a freely selected mu<0.
2. **Actual selected ground:** mu is the actual even successor bottom, the
   successor is bad, both relevant predecessors are nonnegative, the strict
   even selection holds, and all aligned residual-state conditions required
   by the retained theorem are satisfied.

`CrossParityTrialReconstruction.lean` defines Gamma and Alpha on the broader
negative-shift class. Their realness and affine identity hold on that class
as well. These identities do not establish that the chosen shift satisfies
the even secular-root equation or equals the selected negative eigenvalue.
`GlobalParityBottomCrossParity.lean` specializes the construction at the
actual bottom with the extra ground and branch conditions.

Consequently, section 15.11's proposed census needs these corrected rules:

- A genuine-zeta Gamma value outside [0,1] on an arbitrary negative-shift row
  falsifies the all-shifts law. It falsifies the selected-ground law only if
  that row independently satisfies every selected-ground eligibility
  condition. Never silently replace a falsified stronger law by a weaker one.
- If no eligible genuine negative-ground row is established, record the
  selected-ground law as **NOT TESTED**. A sampled generic-ray slack is not
  measured slack for the selected-ground law; a vacuous panel supplies none.
- If all tested controls also remain in [0,1], record **NO DISCRIMINATION
  OBSERVED ON THIS PANEL**. Finite observations do not establish universal
  genericity or justify a mathematical REDUNDANT label. Such a label requires
  an independent theorem or an exact existing implication.
- Report generic and eligible-ground rows separately, including predecessor,
  secular, eigenvalue, parity, alignment and source checks. Preserve negative
  controls that miss the requested witness class rather than treating them as
  successful selected-state falsifiers.

The same distinction explains WP6: its opposite source signs falsify the
unrestricted admissible-ray sign law, not a law restricted to the actual
selected #247 negative ground. This review adds no arithmetic exclusion and
does not run the later Gamma census.

## Radius and finite-window composition

The exact M66 radius is `1/(2*pi^2*(2*K+1)*K^2)`. It gives
`epsilon_2=1/(40*pi^2)>1/400`, which bridges the K2 gap to M51. For K3,
`epsilon_3=1/(126*pi^2)<1/512`, so the present radius supplies no extra K3
window beyond the already proved tiny-aperture base. An arbitrary-radius
interface prepares reuse of a future independently proved curvature radius;
it does not prove a larger one.

Even a complete finite K2/K3 interval certificate cannot exclude the cofinal
counterexample families with unbounded aperture and variable carrier size.
The existing RH-equivalent global exclusion remains OPEN.

## A countermodel preserving the new finite window (DERIVED)

Keep the pole and arch terms and every true prime weight except at powers of
17. Put `Lambda_A(17^j)=A*log17` for j>=1, with A>1 fixed once. All source
matrices at L<=log16, for every K, are unchanged: no altered atom has entered
the window. Thus every newly obtained finite-window certificate is preserved.

The legal K2 even coefficients `(1,-4,6,-4,1)` have moments of degrees 0,1,2
equal to zero and give

`f_L(x)=16*sin(pi*x/L)^4/sqrt(L)` on [0,L], with squared norm 70.

For 0<t<L, `H_L(t)=integral_0^(L-t) f_L(x+t)*f_L(x) dx>0`. At a fixed
`log17<L0<2*log17`, only the changed primary atom 17 enters. The exact prime
channel therefore gives

`E_A(L0)=E_1(L0)-(A-1)*D`, where `D=2*log17*H_L0(log17)/sqrt(17)>0`.

Taking `A=2+max(E_1(L0),0)/D` makes `E_A(L0)<=-D<0`. Unit normalization
divides E and D by 70 and does not change this threshold. This is an exact
algebraic/analytic consequence, not a separately formalized Lean theorem or
a completed numerical experiment.

The control preserves positive prime-power-consistent weights and the whole
finite window, while deliberately violating genuine von Mangoldt arithmetic
at 17. It does not preserve all hardcoded canonical theorem hypotheses or
historical probes above log17, and is not a zeta counterexample. Its purpose
is to falsify propagation based solely on finite-window values and generic
positive weights. The fastest later experiment is the one-atom difference
at L0=3 together with exact unchanged matrices below log16; no extra WP6
family is run in this PR.
