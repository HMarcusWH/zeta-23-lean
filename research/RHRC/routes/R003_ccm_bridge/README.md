# R003 — CCM / finite Weil bridge

Status: **ACTIVE. FIRST-BAD SHELL/KKT + RANK-ONE PARITY DEFECT PROVED; SCALAR RIGIDITY NEXT. RH OPEN.**

## Current authority

~~~text
theorem-state anchor = PR #110 merge 07e0c845d128831b244b13503c9640b934bf4416
validated theorem head = ca0c389827520e2005390637742389819dc97068
validated theorem tree = f2e9985ac976c83ecfa7f5dbce64b1e0193680b0
live main at sync start = 07e0c845d128831b244b13503c9640b934bf4416
theorem-bearing merged through = PR #110
RHRC #738 = SUCCESS
Permansson #511 = SUCCESS
CCM/ExceptionalZero/no-placeholder/source-firewall gates = SUCCESS
#110 promoted theorem-specific axiom surface = revalidated by this control-plane PR
RH = OPEN
~~~

## Closed internal ladder

~~~text
F1 finite canonical obstruction                           PROVED
K0-F1/K0-F1E constrained + Euclidean finite wall          PROVED
N-FLOW fixed-L negative tail                              PROVED / #100
PARITY reversal / displacement collapse                   PROVED / #102
PARITY-FLOW D-equivalence / exact parity geometry          PROVED / #103
PARITY-BAD least bad size + predecessor nonnegative        PROVED / #105
PARITY-BAD 1D successor shell                              PROVED / #105
FIRST-BAD-SPECTRUM orthogonal compression                  PROVED / #107
FIRST-BAD-SPECTRUM negative Rayleigh eigenmode             PROVED / #107
FIRST-BAD-SPECTRUM successor predecessor nonnegativity     PROVED / #107
FIRST-BAD-SPECTRUM negative mode not inherited             PROVED / #107
FIRST-BAD-SPECTRUM off-line-zero endpoint                  PROVED / #107
FIRST-BAD-RIGIDITY-A nonzero ambient shell projection      PROVED / #109
FIRST-BAD-RIGIDITY-B exact parity normal spaces            PROVED / #109
FIRST-BAD-RIGIDITY-B exact parity KKT residual             PROVED / #109
off-line zero -> shell + KKT first-bad endpoint            PROVED / #109
FIRST-BAD-RIGIDITY-C Euclidean algebraic D-equivalence     PROVED / #110
FIRST-BAD-RIGIDITY-C g_N=P_-d³ != 0 for N>=2              PROVED / #110
FIRST-BAD-RIGIDITY-C range(T_-D-DT_+) <= C g_N            PROVED / #110
FIRST-BAD-RIGIDITY-C defect finrank <=1                    PROVED / #110
FIRST-BAD-RIGIDITY-C conjugated defect finrank <=1         PROVED / #110
~~~

## Next route state — FIRST-BAD-RIGIDITY-D

1. Internalize the centered predecessor image inside the successor parity subtype and construct the native one-dimensional shell complement.
2. Decompose the first-bad negative eigenmode as predecessor component plus a nonzero shell coefficient.
3. Prove `A - lam I` invertible from predecessor nonnegativity and `lam < 0`.
4. Derive the shifted scalar Schur/Feshbach equation.
5. Strengthen #110's one-line range theorem to an explicit factorization `F_N = g_N ⊗ ell_N` if the defect functional can be isolated cleanly.
6. Pull `g_N` back through the algebraic D-equivalence and compare its component with the first-bad successor shell.
7. Formalize the parity nullity-difference bound `<=1` under algebraic conjugation.
8. Package the common-resonance vs one-channel-resolvent dichotomy.
9. Attack / classify simultaneous even-odd resonance at a first bad state.

## Derived but not promoted

~~~text
negative index(T_first-bad) = 1
unique negative eigenline
parity nullity difference at a fixed scalar <= 1
away from common resonance, the parity eigenvector lies in one resolvent channel
~~~

These remain **DERIVED / OPEN FORMALIZATION**, not PROVED claims.

## #109/#110 composition clue

Two one-dimensional structures are now available in the same finite-wall problem:

~~~text
N-flow first-bad shell:      dim_C S = 1 and P_S(v_bad) != 0
parity compression defect:   range(T_-D-DT_+) <= C g_N, g_N=P_-d³
~~~

**LEAD / HYPOTHESIS:** after pulling the cubic channel back through D, its projection onto the first-bad shell may be nonzero. If theoremized, the shell channel and parity-defect channel would meet in the same one-dimensional successor obstruction.

This is not yet a proved shell-alignment theorem.

## Firewalls

- D is not unitary or isometric.
- #109 proves ambient shell projection, not the native successor-subtype block decomposition.
- `v ∉ W` does not mean `v ∈ W^perp`.
- the one-dimensional shell is not proved T-invariant.
- `finrank <=1` does not mean exact rank one.
- `g_N != 0` does not imply the defect map is nonzero.
- algebraic conjugation does not authorize Hermitian interlacing/inertia claims without a compatible inner product theorem.
- use `A - lam I` for `lam < 0`; never assume `A⁻¹` at zero.
- no Schur/Feshbach contradiction, positivity theorem, finite-to-infinite theorem or RH theorem is proved.

**RH remains OPEN.**
