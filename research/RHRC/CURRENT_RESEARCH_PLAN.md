# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

## Current theorem-state anchor

~~~text
theorem-state anchor = PR #110 merge 07e0c845d128831b244b13503c9640b934bf4416
validated theorem head = ca0c389827520e2005390637742389819dc97068
validated theorem tree = f2e9985ac976c83ecfa7f5dbce64b1e0193680b0
live main at sync start = 07e0c845d128831b244b13503c9640b934bf4416
theorem-bearing merged through = PR #110
RHRC #738 = SUCCESS
Permansson #511 = SUCCESS
CCM build = SUCCESS
ExceptionalZero build = SUCCESS
normalization/source firewall = SUCCESS
forbidden-placeholder gate = SUCCESS
#109 printed axiom surface = [propext, Classical.choice, Quot.sound]
#110 promoted theorem-specific axiom surface = revalidated by this control-plane PR
sorryAx/project axioms = absent by authoritative gates
RH = OPEN
~~~

## One-screen frontier

~~~text
DONE
  W0/W1/W2-ZS + finite legal approximation
  F1 canonical finite negative obstruction
  constrained algebra / Hermitianity / displacement
  Euclidean constrained sector
  exact centered N-flow
  fixed-L negative constrained tail
  exact reversal symmetry
  direct parity decomposition
  D : V_N^+ ≃ V_N^-
  exact parity dimensions N-1/N-1
  D_M E = E D_N
  exact parity quadratic split
  fixed bad parity tail
  least bad parity size >=2
  predecessor parity sector nonnegative
  exact 1D Euclidean successor parity shell
  parity-constrained Euclidean compression
  exact compressed/self quadratic equality
  compressed symmetry
  ParityBad -> negative Rayleigh eigenmode
  predecessor nonnegativity transported into successor matrix
  negative successor eigenmode not inherited
  off-line zero -> first-bad negative spectral endpoint
  nonzero projection of the negative mode to the 1D ambient successor shell
  exact parity normal spaces
    even residual normal = span{1,d²}
    odd residual normal = span{d}
  exact parity KKT residual
  off-line zero -> first-bad shell + KKT endpoint
  Euclidean algebraic D-equivalence V_N^+ ≃ V_N^- for N>=1
  M(Du)=D(Mu) on the even constrained sector
  explicit odd cubic channel g_N = P_- d³
  g_N != 0 for N>=2
  range(T_- D - D T_+) <= C g_N
  finrank range(T_- D - D T_+) <= 1
  finrank range(E^-1 T_- E - T_+) <= 1

NOW — FIRST-BAD-RIGIDITY-D
  internalize predecessor W inside the successor parity subtype V
  build the native decomposition V = W ⊕ S with dim_C S = 1
  write the first-bad eigenmode as w + alpha*s and theorem-lock alpha != 0
  prove A - lam I invertible from A >= 0 and lam < 0
  derive the shifted scalar Schur/Feshbach equation
  strengthen the parity defect to an explicit rank-one factorization when possible
    F_N = g_N ⊗ ell_N
  pull the cubic channel back through E and compare it with the first-bad shell
  theoremize the parity nullity-difference <= 1 consequence
  package the common-resonance vs one-channel-resolvent dichotomy

THEN
  attack / classify simultaneous even-odd resonance at a first bad state
  compose the scalar shell and scalar parity-defect channels
  test whether the first-bad state is impossible

PARALLEL SOURCE
  G1-B1B -> G1-final -> S-NEG -> G23

RH OPEN
~~~

## Why FIRST-BAD-RIGIDITY-D is next

PR #109 closes the shell/KKT package in the ambient Euclidean formulation: the distinguished negative first-bad eigenmode has a nonzero projection to the already-proved one-dimensional successor shell, the parity normal spaces are exact, and the KKT residual is explicit.

PR #110 then composes the even KKT-normal geometry with the exact even commutator collapse. After applying D, the even normal channel `span{1,d²}` becomes `span{d,d³}`; odd compression kills the `d` component, leaving only the projected cubic channel `g_N = P_- d³`. Lean proves the resulting even-to-odd compressed intertwining defect has range in `C g_N` and finrank at most one, and the same rank bound survives algebraic conjugation back to the even sector.

The remaining first-bad problem is therefore not an arbitrary finite spectral problem. It has two one-dimensional structures available for composition: the successor N-flow shell and the parity-compression defect channel.

## Exact boundary on what #109 did not prove

The successful #109 implementation keeps the predecessor/shell argument in the ambient Euclidean space. It does **not** yet provide the fully intrinsic successor-subtype block decomposition needed for a native Schur complement. That intrinsic block geometry remains part of FIRST-BAD-RIGIDITY-D.

Negative index exactly one / uniqueness of the negative eigenline also remains **DERIVED / OPEN FORMALIZATION** unless separately theorem-locked.

## Rank-one defect firewalls

- `finrank <= 1` does not mean the defect is nonzero or has rank exactly one.
- `g_N != 0` does not by itself prove the defect functional is nonzero.
- the Euclidean D-equivalence is algebraic, not unitary or isometric.
- conjugating the odd compression through D therefore does not automatically give a self-adjoint operator in the original even-sector inner product.
- equal spectra, Hermitian rank-one interlacing and inertia transport do not follow from #110.

## Schur firewall

The predecessor block may be semidefinite. The safe future equation uses `A - lam I` for `lam < 0`:

~~~text
c - lam - b* (A - lam I)^(-1) b = 0
~~~

Never replace this with an `A⁻¹` formula at zero without a separate invertibility theorem.

**RH remains OPEN.**
