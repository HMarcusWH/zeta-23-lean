# R003 — CCM / finite Weil bridge

Status: **ACTIVE. FIRST-BAD SPECTRAL ENDPOINT PROVED; RIGIDITY NEXT. RH OPEN.**

## Current authority

~~~text
theorem-state anchor = PR #107 merge b7d1022e33e2177c5597d008f593d3684d0ec720
validated theorem head = cfcf397cc8c15dbb368fbee3a161b8733061b770
validated synthetic merge = 19cd290510fe4fb1d253522c29644ff3e4563c03
validated theorem tree = 719b45162fd0814581759661f12eab16c46e1201
live main = b7d1022e33e2177c5597d008f593d3684d0ec720
theorem-bearing merged through = PR #107
RHRC #717 = SUCCESS
Permansson #490 = SUCCESS
axioms = [propext, Classical.choice, Quot.sound]
sorryAx = absent
date = 2026-09-03
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
FIRST-BAD-SPECTRUM exact self-form agreement               PROVED / #107
FIRST-BAD-SPECTRUM compressed symmetry                     PROVED / #107
FIRST-BAD-SPECTRUM negative Rayleigh eigenmode             PROVED / #107
FIRST-BAD-SPECTRUM successor predecessor nonnegativity     PROVED / #107
FIRST-BAD-SPECTRUM negative mode not inherited             PROVED / #107
FIRST-BAD-SPECTRUM off-line-zero endpoint                  PROVED / #107
~~~

## Next route state — FIRST-BAD-RIGIDITY

1. Internalize the centered predecessor image inside the successor parity subtype.
2. Prove its intrinsic orthogonal complement has complex finrank one.
3. Turn `v ∉ W` into an explicit nonzero shell projection.
4. Prove negative index one / unique negative eigenline if cheap.
5. Prove parity-specific normal spaces: even `span{1,d²}`; odd `span{d}`.
6. Derive the parity KKT residual.
7. Derive the shifted scalar Schur/Feshbach equation.
8. Combine even KKT with `[D,M]u=0` and isolate the projected `d³` defect.

## Derived but not promoted

~~~text
P_shell(v) != 0
negative index(T) = 1
unique negative eigenline
~~~

These remain **DERIVED / OPEN FORMALIZATION**, not PROVED claims.

## Firewalls

- D is not unitary.
- `v ∉ W` does not mean `v ∈ W^perp`.
- the one-dimensional shell is not proved T-invariant.
- use `A - lam I` for `lam < 0`; never assume `A⁻¹`.
- no KKT contradiction, positivity theorem, finite-to-infinite theorem or RH theorem is proved.

**RH remains OPEN.**
