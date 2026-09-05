# RHRC formal audit — merged through FIRST-BAD-RIGIDITY-E1 / PR #115

> **RH remains OPEN.**

## Current merged authority

~~~text
theorem-state anchor = PR #115 merge a2fecffbef8fed1fdfba373aa5756acf2618e2a1
theorem tree = 47a2601e3464b0b4248e61c52b4560681f73c986
theorem-bearing merged through = PR #115
FIRST-BAD-RIGIDITY-E1 cubic-shell incidence = PROVED / MERGED
Lean = 4.33.0-rc2
RH = OPEN
~~~

Live GitHub head + exact Lean/CI build closure remain authoritative over this audit summary.

## PR #112 — FIRST-BAD-RIGIDITY-D1

**PROVED:**
- `AnyParityBad` and a global least-bad finite size;
- both parity sectors nonnegative at every smaller size, including the predecessor of the global first bad state;
- intrinsic predecessor subspace inside the exact successor parity carrier;
- intrinsic one-step shell of complex finrank one;
- predecessor plus intrinsic shell spans the successor carrier;
- first-bad negative eigenmode has a decomposition with nonzero intrinsic shell component;
- canonical cubic defect functional;
- exact pointwise factorization of the compressed parity defect through the explicit cubic generator;
- nonzero cubic generator for `N>=2`;
- nonzero algebraic pullback of the cubic generator through D;
- ExceptionalZero endpoint packaging global first badness, KKT, intrinsic shell and exact cubic factorization at the same finite state forced by an off-line zero.

**Not proved by #112:** the defect functional is nonzero, exact rank one, D-unitarity, shell invariance, shifted Schur closure, negative index exactly one, positivity, finite-to-infinite closure or RH.

## PR #113 — FIRST-BAD-RIGIDITY-D2

**PROVED:**
- intrinsic predecessor and successor shell are complementary;
- canonical intrinsic direct-sum coordinates `W × S ≃ V`;
- canonical `intrinsicPredecessorPart` and `intrinsicShellPart`;
- exact reconstruction;
- `intrinsicShellPart_eq_zero_iff`: shell coordinate vanishes exactly on W;
- predecessor/shell orthogonality;
- first-bad negative eigenmode has nonzero canonical shell coordinate;
- projected predecessor block `A=P_W T|_W` and shell coupling `B=P_W T|_S` without W/S invariance assumptions;
- predecessor nonnegativity descends to A's self-inner form;
- for real `lam<0`, `A-lam I` is bijective;
- safe shifted predecessor equivalence/resolvent;
- first-bad block equation `(A-lam I)w=-Bs`;
- exact predecessor reconstruction `w=-(A-lam I)^(-1)Bs`;
- basis-free scalar shifted Schur identity;
- ExceptionalZero endpoint putting global first badness, both predecessor parities nonnegative, negative eigenpair, intrinsic shell, KKT, exact cubic factorization and shifted Schur reduction at one common finite problem.

## PR #115 — FIRST-BAD-RIGIDITY-E1

~~~text
merge/main = a2fecffbef8fed1fdfba373aa5756acf2618e2a1
merged tree = 47a2601e3464b0b4248e61c52b4560681f73c986
~~~

**PROVED:**
- every vector inherited from the centered intrinsic predecessor has zero coordinate on the new outer index;
- the odd cubic compression vector has a nonzero new outer coordinate in the stated nontrivial range;
- the odd cubic generator is not a centered predecessor extension;
- Euclidean D/N-flow compatibility needed for the algebraic even pullback;
- the corresponding even successor cubic vector is also not inherited;
- parity-uniform `successorParityCubicVector` / canonical `intrinsicCubicShellPart`;
- main E1 endpoint

~~~text
intrinsicCubicShellPart p N != 0
~~~

for every parity and the stated `N>=1` range;
- ExceptionalZero endpoint adding that nonzero cubic shell coordinate to the same global-first-bad finite state already carrying #113's negative-mode shell coordinate and shifted Schur identity.

**Deliberately not proved by #115:**
- the optional closed form `alpha_K = (3K^2+3K-1)/5`;
- cubic vector is pure shell;
- shell invariance;
- D is unitary/isometric;
- `cubicDefectFunctional != 0`;
- exact defect rank one;
- cubic-normalized Schur rigidity;
- resolvent monotonicity;
- simultaneous parity-resonance exclusion;
- positivity, finite-to-infinite closure, or RH.

## Current formal state

~~~text
least bad parity + predecessor nonnegative + 1D ambient shell        PROVED / #105
parity-constrained compression + negative eigenmode                  PROVED / #107
nonzero ambient successor-shell projection + exact KKT               PROVED / #109
algebraic D-equivalence + cubic defect range/finrank <=1             PROVED / #110
global first bad + both predecessor parities nonnegative             PROVED / #112
intrinsic predecessor W + intrinsic shell S, dim_C S=1               PROVED / #112
exact cubic factorization F_N(v)=ell_N(v) g_N                        PROVED / #112
canonical direct sum V=W⊕S                                            PROVED / #113
negative mode canonical shell coordinate !=0                         PROVED / #113
A-lam I bijective for lam<0                                          PROVED / #113
shifted predecessor reconstruction                                   PROVED / #113
scalar shifted Schur identity                                        PROVED / #113
canonical cubic shell coordinate !=0                                 PROVED / #115
off-line zero -> same global-first-bad Schur+cubic+E1 endpoint       PROVED / #115

cubic-normalized scale-free Schur equation                           DERIVED INTERFACE / OPEN FORMALIZATION
projected predecessor block symmetric                                DERIVED / OPEN FORMALIZATION
negative index exactly one / unique negative line                    DERIVED / OPEN FORMALIZATION
shifted resolvent positivity / monotonicity                           DERIVED / OPEN FORMALIZATION
parity nullity-difference <=1                                        DERIVED / OPEN FORMALIZATION
common-resonance vs one-channel-resolvent dichotomy                  DERIVED / OPEN FORMALIZATION
simultaneous parity-resonance exclusion/classification               OPEN
deformation-budget asymptotics / infinite-tail certificate           LEAD / HYPOTHESIS
positivity / finite-to-infinite closure                              OPEN
RH                                                                    OPEN
~~~

## Current research frontier

The next theorem target is E1b/E2. #113 and #115 now give two independently constructed nonzero vectors in the same one-dimensional intrinsic shell:

~~~text
negative-mode shell coordinate != 0
canonical cubic shell coordinate != 0
dim_C S = 1
~~~

The immediate composition target is to identify these vectors up to a nonzero scalar, transfer the shifted Schur identity to the canonical cubic shell line, and normalize away only scalar choice.

E3 then targets projected symmetry, quantitative shifted coercivity and resolvent consequences. E4 targets algebraic parity nullity and the common-resonance versus one-channel-resolvent dichotomy.

## Parallel deformation-budget diagnostic

PR #116 adds research-control infrastructure for a separate paper-level search-contraction lead. It treats exact N-flow as a nested spectral process and distinguishes:

~~~text
local one-step deformation information
complete remaining tail budget
certified positive headroom
~~~

A small local deformation rate is not a tail theorem. A decision-bearing prune requires a certified positive lower margin and a certified upper bound for the entire remaining deformation budget.

The supporting controller is explicitly non-authoritative: it cannot promote Lean theorems, write RH claim authority or emit the terminal RH answer.

## Permanent firewalls

- `V=W⊕S` is proved; shell invariance is not.
- nonzero shell coordinate does not imply the vector is pure shell.
- D is algebraic, not unitary or isometric.
- exact cubic factorization does not prove the scalar functional nonzero or the defect rank exactly one.
- algebraic conjugation does not automatically preserve self-adjointness in the original even-sector metric.
- equal spectra, Hermitian interlacing and inertia transport through D are not proved.
- use `A-lam I` for `lam<0`; never replace it by `A^-1` at zero without a separate theorem.
- negative-index-one remains derived, not theorem-locked.
- the shifted Schur identity by itself is not a contradiction; ordinary finite Hermitian systems can satisfy it with a negative eigenvalue.
- Control-v2 diagnostics, retroactive clues and route recommendations are not theorem evidence.
- no positivity theorem, finite-to-infinite theorem or RH theorem exists.

Detailed current research implications and falsification plan: `research/RHRC/RESEARCH_LEADS_POST_115_DELTA.md`.

**RH remains OPEN.**
