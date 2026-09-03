# RHRC formal audit — merged through FIRST-BAD-RIGIDITY-C / PR #110

> **RH remains OPEN.**

## Current merged authority

~~~text
theorem-state anchor = PR #110 merge 07e0c845d128831b244b13503c9640b934bf4416
validated theorem head = ca0c389827520e2005390637742389819dc97068
validated theorem tree = f2e9985ac976c83ecfa7f5dbce64b1e0193680b0
live main at sync start = 07e0c845d128831b244b13503c9640b934bf4416
theorem-bearing merged through = PR #110
RHRC #738 = SUCCESS
Permansson #511 = SUCCESS
Lean = 4.33.0-rc2
python RHRC suite = SUCCESS
R003 normalization/source firewall = SUCCESS
CCM build = SUCCESS
ExceptionalZero build = SUCCESS
forbidden-placeholder gate = SUCCESS
#109 printed axiom surface = [propext, Classical.choice, Quot.sound]
#110 promoted theorem-specific axiom surface = revalidated by this control-plane PR
RH = OPEN
~~~

## Exact PR #110 validation

~~~text
base/main = 8a67b9e3824cff2f408c9fbd48c7ce8d26c5dcb8
final theorem head = ca0c389827520e2005390637742389819dc97068
merge/main = 07e0c845d128831b244b13503c9640b934bf4416
validated/merged theorem tree = f2e9985ac976c83ecfa7f5dbce64b1e0193680b0
RHRC #738 = SUCCESS
Permansson #511 = SUCCESS
python RHRC suite = SUCCESS
R003 normalization/source firewall = SUCCESS
CCM build = SUCCESS
ExceptionalZero build = SUCCESS
forbidden-placeholder gate = SUCCESS
~~~

The final #110 repair changed only proof shape: it isolated the star-projection equality before rewriting and kept the conjugated-defect proof at `LinearMap.ext` subtype level. The theorem statements were not weakened. Both repository workflows then passed on exact head `ca0c3898...`, and merged main has the identical theorem tree.

## PR #109 formally validated surface

**PROVED:**
- `paritySuccShellProjection_ne_zero_of_not_embedded`;
- `negative_eigenmode_paritySuccShell_projection_ne_zero`;
- `re_inner_successor_nonnegative_on_embeddedPredecessor`;
- exact even normal `(V+)ᗮ ∩ E+ = span{1,d²}`;
- exact odd normal `(V-)ᗮ ∩ E- = span{d}`;
- `parityKKTResidual_of_eigenmode`;
- `exists_firstBadParity_shell_KKT_of_offLine_zero` and existential wrapper.

The successful implementation keeps the successor shell in the ambient Euclidean space. It does not yet theoremize a fully intrinsic successor-subtype block decomposition.

## PR #110 formally validated surface

**PROVED:**
- Euclidean centered-index linear map and restriction `V_N^+ -> V_N^-`;
- injectivity and, for `N>=1`, surjectivity / algebraic `LinearEquiv`;
- arbitrary even compression residual in the exact even normal channel `span{1,d²}`;
- exact Euclidean lift `M(Du)=D(Mu)` on the even constrained sector;
- explicit odd cubic compression vector `g_N = P_- d³`;
- `g_N != 0` for `N>=2`;
- pointwise defect values are scalar multiples of `g_N`;
- `range(T_- D - D T_+) <= C g_N`;
- `finrank range(T_- D - D T_+) <= 1`;
- after algebraic conjugation through D, the same-space parity defect has finrank at most one.

The final #110 source did not retain its earlier module-local `#print axioms` lines. This control-plane PR restores theorem-specific `#check/#print axioms` coverage through `Zeta23/CCM/ClaimBindings.lean`; those outputs become promotion authority only after this PR's Lean gate succeeds.

## Current formal state

~~~text
least bad parity + predecessor nonnegative + 1D shell         PROVED / #105
parity-constrained compression                                PROVED / #107
negative constrained eigenmode                                PROVED / #107
negative first-bad eigenmode not inherited                    PROVED / #107
nonzero ambient successor-shell projection                    PROVED / #109
exact parity normal spaces                                    PROVED / #109
exact parity KKT residual                                     PROVED / #109
off-line zero -> first-bad shell + KKT endpoint               PROVED / #109
Euclidean algebraic D-equivalence                             PROVED / #110
explicit cubic odd compression channel                        PROVED / #110
compressed parity intertwining defect finrank <= 1            PROVED / #110
conjugated same-space parity defect finrank <= 1              PROVED / #110

intrinsic successor-subtype block decomposition               OPEN
negative index one / unique negative eigenline                DERIVED / OPEN FORMALIZATION
exact nonzero rank-one factorization                          OPEN
shifted scalar Schur/Feshbach rigidity                        OPEN
simultaneous parity-resonance exclusion/classification        OPEN
RH                                                             OPEN
~~~

## Permanent firewalls

- #109 proves nonzero projection to the ambient one-dimensional shell, not a pure-shell eigenvector or shell invariance.
- the native successor-subtype predecessor/shell decomposition remains open.
- D is algebraic, not unitary or isometric.
- `finrank <= 1` does not prove the defect is nonzero or has rank exactly one.
- `g_N != 0` does not prove the scalar defect functional is nonzero.
- algebraic same-space conjugation does not automatically preserve self-adjointness in the original even-sector inner product.
- equal spectra, Hermitian rank-one interlacing and inertia transport are not proved.
- use `A - lam I` for `lam < 0`, not `A⁻¹` at zero.
- negative-index-one remains derived, not theorem-locked.
- no Schur/Feshbach contradiction, positivity theorem, finite-to-infinite theorem or RH theorem exists.

**RH remains OPEN.**
