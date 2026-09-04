# RHRC formal audit — merged through FIRST-BAD-RIGIDITY-D2 / PR #113

> **RH remains OPEN.**

## Current merged authority

~~~text
theorem-state anchor = PR #113 merge d3b62817711c4c97f0d817c8b4a4ac0bc646d733
validated theorem head = 2da46eed0068613d904bc67e20790f46bc46818e
validated theorem tree = 066f5f51041b302dfa1a66d84a024660a09acbf5
theorem-bearing merged through = PR #113
RHRC #761 = SUCCESS
Permansson #534 = SUCCESS
Lean = 4.33.0-rc2
python RHRC suite = SUCCESS
R003 normalization/source firewall = SUCCESS
CCM build = SUCCESS
ExceptionalZero build = SUCCESS
forbidden-placeholder gate = SUCCESS
RH = OPEN
~~~

The final #113 validated head and merged main share the same theorem tree. This audit therefore treats the exact #113 branch tree as the merged theorem authority.

## PR #112 — FIRST-BAD-RIGIDITY-D1

~~~text
final theorem head = d236f0b8dd38eabb224eef14293f4a62006dfdcc
merge/main = c16da339476480773e7827aa597934073da398a4
RHRC #752 = SUCCESS
Permansson #525 = SUCCESS
~~~

**PROVED:**
- `AnyParityBad` and a global least-bad finite size;
- both parity sectors nonnegative at every smaller size, including the predecessor of the global first bad state;
- intrinsic predecessor subspace inside the exact successor parity carrier;
- intrinsic one-step shell linearly equivalent to the ambient shell and of complex finrank one;
- predecessor plus intrinsic shell spans the successor carrier;
- first-bad negative eigenmode has a decomposition with nonzero intrinsic shell component;
- canonical cubic defect functional;
- exact pointwise factorization of the compressed parity defect through the explicit cubic generator;
- nonzero cubic generator for `N>=2`;
- nonzero algebraic pullback of the cubic generator through D;
- ExceptionalZero endpoint packaging global first badness, KKT, intrinsic shell and exact cubic factorization at the same finite state forced by an off-line zero.

**Not proved by #112:** the defect functional is nonzero, exact rank one, D-unitarity, shell invariance, shifted Schur closure, negative index exactly one, positivity, finite-to-infinite closure or RH.

## PR #113 — FIRST-BAD-RIGIDITY-D2

~~~text
base/main = c16da339476480773e7827aa597934073da398a4
final theorem head = 2da46eed0068613d904bc67e20790f46bc46818e
merge/main = d3b62817711c4c97f0d817c8b4a4ac0bc646d733
validated/merged theorem tree = 066f5f51041b302dfa1a66d84a024660a09acbf5
RHRC #761 = SUCCESS
Permansson #534 = SUCCESS
python RHRC suite = SUCCESS
R003 normalization/source firewall = SUCCESS
CCM build = SUCCESS
ExceptionalZero build = SUCCESS
forbidden-placeholder gate = SUCCESS
~~~

**PROVED:**
- `intrinsicPredecessor_disjoint_shell`;
- `intrinsicPredecessor_isCompl_shell`;
- canonical intrinsic direct-sum coordinates `W × S ≃ V`;
- canonical `intrinsicPredecessorPart` and `intrinsicShellPart`;
- exact reconstruction `predecessorPart + shellPart = v`;
- `intrinsicShellPart_eq_zero_iff`: shell coordinate vanishes exactly on W;
- predecessor/shell orthogonality;
- `negative_eigenmode_intrinsicShellPart_ne_zero`;
- projected predecessor block `A=P_W T|_W` and shell coupling `B=P_W T|_S`, with no W- or S-invariance assumption;
- predecessor nonnegativity descends to A's self-inner form;
- for real `lam<0`, `A-lam I` has trivial kernel, is injective and is bijective in finite dimension;
- safe shifted predecessor equivalence/resolvent;
- first-bad block equation `(A-lam I)w=-Bs`;
- exact predecessor reconstruction `w=-(A-lam I)^(-1)Bs`;
- basis-free scalar shifted Schur identity;
- `negative_eigenmode_shiftedSchur_package`;
- ExceptionalZero endpoint `exists_globalFirstBad_shiftedSchur_cubicFactorization_of_offLine_zero`, which places global first badness, both predecessor parities nonnegative, negative eigenpair, intrinsic one-dimensional shell, KKT, exact cubic factorization, shifted inverse reconstruction and the scalar Schur identity at one common finite problem.

The final repair on exact head `2da46eed...` changed only proof closure in `eigenmode_shiftedSchur_identity`: after real/complex scalar normalization the remaining goal was reflexive and was discharged by `rfl`. No theorem statement, definition or mathematical hypothesis changed.

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
off-line zero -> same global-first-bad Schur+cubic endpoint          PROVED / #113

projected predecessor block symmetric                                DERIVED / OPEN FORMALIZATION
negative index exactly one / unique negative line                    DERIVED / OPEN FORMALIZATION
cubic generator has nonzero intrinsic shell coordinate               LEAD / HYPOTHESIS
cubic-normalized scale-free Schur equation                           LEAD / HYPOTHESIS
shifted resolvent positivity / monotonicity                           DERIVED / OPEN FORMALIZATION
parity nullity-difference <=1                                        DERIVED / OPEN FORMALIZATION
common-resonance vs one-channel-resolvent dichotomy                  DERIVED / OPEN FORMALIZATION
simultaneous parity-resonance exclusion/classification               OPEN
positivity / finite-to-infinite closure                              OPEN
RH                                                                    OPEN
~~~

## Post-green research note

The decisive change after #113 is compositional. There are now two exact one-dimensional structures at the same first-bad state: the intrinsic N-flow shell `S` and the explicit cubic parity-defect line. The scalar Schur equation also lives on the actual nonzero shell coordinate.

The highest-information next test is therefore **cubic-shell incidence**. Because #113 proves `intrinsicShellPart x = 0 <-> x ∈ W`, this can be attacked by proving the cubic generator is not a centered predecessor extension rather than by comparing ambient projections directly.

The current explicit lead is to derive, from the repository's exact odd orthogonal projection,

~~~text
g_K = d^3 - alpha_K d,
alpha_K = (3K^2+3K-1)/5,
(g_K)_(+K) = K(K-1)(2K-1)/5.
~~~

If the exact formula survives verification, the nonzero outer coefficient for `K>=2` excludes membership in the centered predecessor image and forces a nonzero canonical shell coordinate. This remains a **LEAD / HYPOTHESIS** until Lean theoremizes the exact projection/indexing calculation.

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
- no positivity theorem, finite-to-infinite theorem or RH theorem exists.

Detailed post-green implications and falsification plan: `research/RHRC/RESEARCH_LEADS_POST_113_DELTA.md`.

**RH remains OPEN.**
