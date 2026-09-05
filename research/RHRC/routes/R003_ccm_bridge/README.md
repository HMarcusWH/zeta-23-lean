# R003 — CCM / finite Weil bridge

Status: **ACTIVE. GLOBAL FIRST-BAD + INTRINSIC SCHUR/CUBIC REDUCTION PROVED THROUGH PR #115; E1b/E2 CURRENT. RH OPEN.**

## Current authority split

~~~text
theorem-state anchor = PR #115 merge a2fecffbef8fed1fdfba373aa5756acf2618e2a1
theorem tree = 47a2601e3464b0b4248e61c52b4560681f73c986
theorem-bearing merged through = PR #115
E1 cubic-shell incidence = PROVED / MERGED

control-plane anchor = PR #116 merge 8921572170e89d74216f0c5577b669696626219e
control-plane tree = fc138b517c6835230515167386eafe3ef3495baf
Control v2 / FFBBP v1.6 assurance = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
~~~

Live GitHub head + exact Lean/CI build closure remain authoritative. PR #116 changed no `Zeta23/**/*.lean` theorem authority.

## Closed internal ladder

~~~text
F1 finite canonical obstruction                                PROVED / #94
constrained / Euclidean finite wall                            PROVED / #96-#98
N-FLOW fixed-L negative tail                                   PROVED / #100
PARITY reversal / displacement collapse                        PROVED / #102
PARITY-FLOW D-equivalence / exact parity geometry               PROVED / #103
PARITY-BAD least bad size + predecessor nonnegative             PROVED / #105
PARITY-BAD one-dimensional ambient successor shell              PROVED / #105
FIRST-BAD-SPECTRUM constrained compression + negative mode      PROVED / #107
FIRST-BAD-SPECTRUM negative mode not inherited                  PROVED / #107
FIRST-BAD-RIGIDITY-A nonzero ambient shell projection           PROVED / #109
FIRST-BAD-RIGIDITY-B exact parity normal spaces + KKT           PROVED / #109
FIRST-BAD-RIGIDITY-C algebraic D-equivalence / cubic channel    PROVED / #110
FIRST-BAD-RIGIDITY-C defect range in C g_N / finrank <=1        PROVED / #110
FIRST-BAD-RIGIDITY-D1 global first bad                          PROVED / #112
FIRST-BAD-RIGIDITY-D1 both predecessor parities nonnegative     PROVED / #112
FIRST-BAD-RIGIDITY-D1 intrinsic W + one-dimensional S           PROVED / #112
FIRST-BAD-RIGIDITY-D1 exact cubic factorization F=ell*g         PROVED / #112
FIRST-BAD-RIGIDITY-D2 V=W⊕S with canonical projections          PROVED / #113
FIRST-BAD-RIGIDITY-D2 shellPart(v_bad) != 0                     PROVED / #113
FIRST-BAD-RIGIDITY-D2 A-lam I bijective for lam<0               PROVED / #113
FIRST-BAD-RIGIDITY-D2 w=-(A-lam I)^(-1)Bs                      PROVED / #113
FIRST-BAD-RIGIDITY-D2 scalar shifted Schur identity             PROVED / #113
FIRST-BAD-RIGIDITY-E1 cubic generator not inherited             PROVED / #115
FIRST-BAD-RIGIDITY-E1 intrinsicCubicShellPart != 0              PROVED / #115
off-line zero -> common global-first-bad Schur+cubic+E1 state   PROVED / #115
~~~

## Exact post-#115 first-bad state

A hypothetical off-critical-line zeta zero forces one finite problem with:

- positive aperture `L`;
- global least-bad successor size;
- both parity sectors nonnegative at the predecessor size;
- a genuine negative parity-compressed eigenpair `(lam,v)` with `lam<0`;
- intrinsic successor carrier decomposition `V=W⊕S` with `dim_C S=1`;
- canonical shell coordinate `s=intrinsicShellPart(v)` and `s!=0`;
- exact parity KKT residual;
- explicit nonzero cubic generator and exact factorization `F_N(z)=ell_N(z) g_N`;
- safe shifted predecessor inverse `(A-lam I)^(-1)`;
- exact predecessor reconstruction from the shell coordinate;
- basis-free scalar shifted Schur identity;
- canonical parity-uniform cubic shell coordinate `c_N=intrinsicCubicShellPart p N` with `c_N!=0`.

This is a finite rigidity package, not an RH proof.

## Current route state — FIRST-BAD-RIGIDITY-E

### E1 — cubic-shell incidence

**PROVED / #115.**

#115 used the exact characterization

~~~text
intrinsicShellPart x = 0  <->  x ∈ W
~~~

to reduce shell incidence to predecessor non-membership. It proves the odd cubic generator is not inherited, transports the statement to the even carrier using only algebraic D/N-flow compatibility, and concludes

~~~text
intrinsicCubicShellPart p N != 0
~~~

for both parities in the stated range.

The optional explicit projection coefficient

~~~text
alpha_K = (3 K^2 + 3 K - 1)/5
~~~

was not needed and remains an optional LEAD unless a later quantitative calculation requires it.

### E1b/E2 — one-dimensional composition and cubic-normalized Schur

This is the current theorem frontier.

At the same first-bad state,

~~~text
intrinsicShellPart p N v != 0
intrinsicCubicShellPart p N != 0
dim_C S = 1.
~~~

Therefore the two shell vectors differ by a nonzero scalar. The immediate target is to theoremize that scalar-multiple relation and rewrite the #113 shifted Schur identity on the canonical cubic shell line.

Prefer scale-free quantities built directly from

~~~text
c_N := intrinsicCubicShellPart p N
~~~

rather than introducing an arbitrary unit-shell basis. Candidate ratios are

~~~text
q_N = Re <T c_N,c_N> / <c_N,c_N>
beta_N^2 = ||B c_N||^2 / <c_N,c_N>.
~~~

These are DERIVED / OPEN FORMALIZATION, not current theorems.

### E3 — shifted predecessor rigidity

**DERIVED / OPEN FORMALIZATION.** Prove projected predecessor block symmetry and quantitative shifted coercivity in the exact repository inner product, then obtain the safe resolvent estimate.

The post-#116 composition target is not merely generic resolvent monotonicity. If E2/E3 supply the expected estimate, they should theoremize the one-step deformation bound used by the paper diagnostic:

~~~text
g_N = q_N-mu_N
d_N = mu_N-lam

d_N(g_N+d_N) <= beta_N^2
~~~

and hence, when `g_N>0`,

~~~text
d_N <= beta_N^2/g_N.
~~~

The current two-by-two square-root expression remains diagnostic until the operator hypotheses are proved.

### E4 — parity nullity and resonance

**DERIVED / OPEN FORMALIZATION.** Rank-at-most-one same-space parity defect should imply parity kernel/nullity difference at most one at each scalar.

Package the eigenmode alternative as

~~~text
common even/odd resonance at lam
OR
one opposite-parity resolvent channel generated by g_N.
~~~

Then attack or classify simultaneous resonance at the global first-bad state using KKT, displacement, cubic and shell data.

## Cheap composition candidate — shell visibility of the exact cubic defect

PR #112 proves

~~~text
F_N(z)=ell_N(z) • g_N.
~~~

PR #115 proves the canonical cubic generator has nonzero intrinsic shell coordinate. Applying the canonical shell projection should therefore yield

~~~text
intrinsicShellPart(F_N z)=0  <->  ell_N(z)=0.
~~~

**Status: DERIVED / OPEN FORMALIZATION.** If cheap, this is worth theorem-locking because it identifies `cubicDefectFunctional` with visibility of the exact parity defect in the unique new N-flow quotient direction. It still does not prove `ell_N` nonzero on a specific vector or exact rank one.

## Deformation-budget composition and falsification lane

PR #116 added a non-authoritative paper/diagnostic controller for the quantities

~~~text
mu_N      predecessor spectral-floor lower information
q_N       canonical shell stiffness
beta_N    shell/predecessor coupling
D_N       one-step downward-deformation upper bound
R_N       complete remaining deformation upper bound
H_N       headroom lower bound = mu_lower_N - R_upper_N.
~~~

The theorem and diagnostic lanes now meet cleanly:

~~~text
#115 cubic shell
 -> E2 normalized Schur
 -> E3 coercive resolvent
 -> certified one-step deformation theorem
~~~

The cheap paper test should first probe

~~~text
g_N=q_N-mu_N,
beta_N,
beta_N^2/g_N
~~~

for both parities and several fixed positive `L` values. The route dies if the gap closes, coupling does not decay usefully, or the ratio does not admit a summable certified majorant.

A finite prefix, fitted tail or local residual is not a complete budget.

### Whole-N rigidity-horizon consequence

Exact N-flow already proves upward persistence of badness. Therefore, for fixed `(L,p)`, a fully certified horizon

~~~text
H_Nstar>0
~~~

would exclude earlier badness by persistence and later badness by the remaining-deformation bound. The strong target is therefore elimination of the entire fixed-`(L,p)` N-axis, not merely contraction to a finite N-window.

All-`L` certification is required eventually; one universal L-independent `Nstar` is not assumed unless separately needed.

## Optional derived theorem

Codimension-one predecessor nonnegativity plus the proved negative successor direction strongly suggests negative index exactly one / a unique negative eigenline.

**Status: DERIVED / OPEN FORMALIZATION.** Formalize if cheap; do not let it block E2/E3.

## Falsification gates

- keep predecessor N and successor N+1 distinct;
- never treat D as unitary/isometric;
- `g_N!=0` does not prove `ell_N!=0`;
- exact factorization does not prove exact nonzero rank one;
- nonzero shell coordinate does not mean the vector is pure shell;
- shell invariance is not proved;
- the scalar Schur equation is not itself a contradiction;
- a diagnostic 2x2 comparison is not an operator theorem;
- `beta_N -> 0` is not enough; the relevant tail scale is approximately `beta_N^2/(q_N-mu_N)`;
- a finite prefix or fitted tail is not an infinite-tail certificate;
- simultaneous parity resonance remains open until theoremically excluded;
- no RH-equivalent arithmetic estimate may be introduced as a disguised auxiliary hypothesis.

## Source-faithful parallel lane

The internal F1/first-bad route has bypassed the old need to obtain source negativity before making finite progress, but the independent source-faithful lane remains useful as a cross-check:

~~~text
G1-B1B -> G1-final -> S-NEG -> G23.
~~~

Do not conflate source geometry/interface with source negativity.

## Permanent normalization / model firewalls

- canonical sign-sensitive object is `canonicalSourceMatrix = cutoffFreeMatrix = sourceEq44Matrix = dictionaryMatrix` under the repaired source convention;
- legacy printed `finiteMatrix` differs by a scalar identity, so absolute eigenvalue/PSD/inertia claims do not transfer by the scalar-shift relation;
- generic R002 smooth taper-grid is not the canonical CCM family except at exact specialization;
- Bombieri zero-height truncations are distinct from deterministic CCM Fourier-mode truncations;
- boundary-flat legality is required for the hard-window C² bridge.

Detailed current implications and hypotheses: `../../RESEARCH_LEADS_POST_116_DELTA.md`.

**RH remains OPEN.**
