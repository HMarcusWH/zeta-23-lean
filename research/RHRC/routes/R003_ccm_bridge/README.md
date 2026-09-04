# R003 — CCM / finite Weil bridge

Status: **ACTIVE. GLOBAL FIRST-BAD + INTRINSIC SCHUR/CUBIC REDUCTION PROVED THROUGH PR #113; CUBIC-SHELL COMPOSITION NEXT. RH OPEN.**

## Current authority

~~~text
theorem-state anchor = PR #113 merge d3b62817711c4c97f0d817c8b4a4ac0bc646d733
validated theorem head = 2da46eed0068613d904bc67e20790f46bc46818e
validated theorem tree = 066f5f51041b302dfa1a66d84a024660a09acbf5
theorem-bearing merged through = PR #113
RHRC #761 = SUCCESS
Permansson #534 = SUCCESS
CCM/ExceptionalZero/no-placeholder/source-firewall gates = SUCCESS
RH = OPEN
~~~

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
off-line zero -> common global-first-bad Schur+cubic endpoint   PROVED / #113
~~~

## Exact post-#113 first-bad state

A hypothetical off-critical-line zeta zero now forces one finite problem with:

- positive aperture `L`;
- global least-bad successor size;
- both parity sectors nonnegative at the predecessor size;
- a genuine negative parity-compressed eigenpair `(lam,v)` with `lam<0`;
- intrinsic successor carrier decomposition `V=W⊕S` with `dim_C S=1`;
- canonical shell coordinate `s=intrinsicShellPart(v)` and `s!=0`;
- exact parity KKT residual;
- explicit nonzero cubic generator `g_N` and exact factorization `F_N(v)=ell_N(v) g_N`;
- safe shifted predecessor inverse `(A-lam I)^(-1)`;
- exact predecessor reconstruction from the shell coordinate;
- basis-free scalar shifted Schur identity.

This is a finite rigidity package, not an RH proof.

## Current route state — FIRST-BAD-RIGIDITY-E

### E1 — cubic-shell incidence

Use #113's exact characterization

~~~text
intrinsicShellPart x = 0  <->  x ∈ W
~~~

to replace an awkward projection-comparison problem by a predecessor non-membership theorem.

Primary odd target:

~~~text
oddCubicCompressionVector (N+1) ∉ intrinsic predecessor at size N
  -> intrinsic cubic shell coordinate != 0.
~~~

Even target: algebraically pull the cubic generator back through D and prove the analogous non-membership. D must remain purely algebraic; no isometry/unitarity assumption is permitted.

### E1 explicit calculation to theoremize or falsify

Because the odd normal space is exactly `span{d}`, the current lead is

~~~text
g_K = d^3 - alpha_K d,
alpha_K = <d,d^3>/<d,d>.
~~~

Centered power sums suggest

~~~text
alpha_K = (3 K^2 + 3 K - 1)/5,
(g_K)_(+K) = K(K-1)(2K-1)/5.
~~~

For `K>=2` the predicted outer coefficient is nonzero. Exact centered predecessor extension has zero in the new outer coordinates, so the formula would prove non-membership immediately.

**Status: LEAD / HYPOTHESIS.** The formula must be derived from the repository's actual `orthogonalProjectionOnto`, complex inner-product convention and successor-size indexing before promotion.

### E1b/E2 — one-dimensional composition and cubic-normalized Schur

If the cubic vector has nonzero canonical shell part, that shell vector and the first-bad eigenmode shell vector are both nonzero elements of the same one-dimensional complex space. Hence they differ by a nonzero scalar.

Because the #113 Schur identity is homogeneous of degree two in the shell vector, normalize away that scalar and rewrite the first-bad secular equation on the canonical cubic shell line.

This is the intended first direct composition of the N-flow shell and parity cubic-defect channel.

### E3 — shifted predecessor rigidity

**DERIVED / OPEN FORMALIZATION:** prove projected predecessor block symmetry and quantitative shifted coercivity

~~~text
Re <(A-lam I)w,w> >= (-lam)||w||^2,   lam<0.
~~~

Then seek resolvent positivity, a norm bound and a Lean-friendly resolvent monotonicity theorem. These are generic block tools; they become RH-relevant only after composition with the special CCM shell/cubic structure.

### E4 — parity nullity and resonance

**DERIVED / OPEN FORMALIZATION:** rank-at-most-one same-space parity defect should imply parity kernel/nullity difference at most one at each scalar.

Package the eigenmode alternative as

~~~text
common even/odd resonance at lam
OR
one opposite-parity resolvent channel generated by g_N.
~~~

Then attack or classify simultaneous resonance at the global first-bad state using KKT, displacement, cubic and shell data.

## Optional derived theorem

Codimension-one predecessor nonnegativity plus the proved negative successor direction strongly suggests negative index exactly one / a unique negative eigenline.

**Status: DERIVED / OPEN FORMALIZATION.** Formalize if cheap; do not let it block E1/E2.

## Falsification gates

- prove the cubic projection formula from the exact projection; do not infer it from parity alone;
- keep predecessor N and successor N+1 distinct;
- verify outer-coordinate vanishing for exact centered zero extension;
- never treat D as unitary/isometric;
- `g_N!=0` does not prove `ell_N!=0`;
- exact factorization does not prove exact nonzero rank one;
- nonzero shell coordinate does not mean the vector is pure shell;
- shell invariance is not proved;
- the scalar Schur equation is not itself a contradiction;
- resolvent monotonicity or a unique negative root would not prove absence of a negative root;
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

Detailed current implications and hypotheses: `../../RESEARCH_LEADS_POST_113_DELTA.md`.

**RH remains OPEN.**
