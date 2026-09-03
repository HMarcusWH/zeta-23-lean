# R003 — CCM / finite Weil bridge

Status: **ACTIVE DISCOVERY ROUTE. INTERNAL F1 + K0-F1 + K0-F1E + N-FLOW + PARITY + PARITY-FLOW GEOMETRY PROVED. RH OPEN.**

## Current authority

~~~text
theorem-state anchor = PR #103 merge c7129b1856ea03cdf8b831ae1424140f8a7d90a9
validated theorem head = af43242f55536a8170bf303b9c9558c6a0fccdcf
validated synthetic merge = 16c5ebaa6d6d7e14df853e9a0771ab5ef3b07aba
theorem tree = 56d082947fac6eb4666d0e0666e2c8bcd3c0a7e8
RHRC #704 = SUCCESS
Permansson #477 = SUCCESS
axioms = [propext, Classical.choice, Quot.sound]
sorryAx = absent
RH = OPEN
~~~

## Closed internal ladder

~~~text
W0/W1/W2-ZS + G1-A                                      PROVED
F0-B1A/B1B/WCONT/F0-B1C-A/B                             PROVED
strict finite sign transfer + F1                        PROVED
K0-F1 constrained algebra / Hermitianity / displacement PROVED
K0-F1E Euclidean sector + negative direction            PROVED
N-FLOW exact centered nesting + negative tail            PROVED
PARITY exact reversal/matrix/moment symmetry             PROVED / #102
PARITY even constrained commutator collapse              PROVED / #102
PARITY-FLOW direct even/odd decomposition                PROVED / #103
PARITY-FLOW D : V+ ≃ₗ V-                                 PROVED / #103
PARITY-FLOW exact N-1 / N-1 dimensions                   PROVED / #103
PARITY-FLOW Euclidean parity-preserving N-flow           PROVED / #103
~~~

## Current finite obstruction state

Any hypothetical off-line zero forces one fixed L>0 and N0>=2 such that every M>=N0 has a nonzero negative vector in the exact Euclidean boundary-flat sector.

The constrained sector now decomposes exactly into even and odd reversal sectors, each of complex dimension N-1, and D gives a complex-linear equivalence from even to odd.

This is not yet a fixed-parity negative obstruction: the exact quadratic parity split and parity-selection theorem remain open.

## Staged parity-badness source

`Zeta23/CCM/ParityBadness.lean` is present on main but is not imported by `Zeta23.CCM`. Its parity-badness persistence, least-bad and one-dimensional-shell declarations are therefore **STAGED / NOT PROVED**.

## Next: fixed parity and one-dimensional first-bad shell

1. Prove D commutes with exact centered N-flow.
2. Prove the even/odd quadratic cross term vanishes for canonicalSourceMatrix.
3. Split any negative constrained witness into a negative even or odd component.
4. Compose with #100/#103 to get one fixed bad parity tail.
5. Compile/promote parity badness, least bad parity and one-dimensional successor shell.
6. Build constrained symmetric compression and extract a negative eigenmode.
7. Prove exact normal space and derive parity-resolved scalar Schur/Feshbach/KKT rigidity.

## Firewalls

- D-equivalence is not unitary and does not imply equal parity spectra.
- ambient [D,M]u=0 does not imply future compressed parity blocks are intertwined.
- the post-#103 shell is not automatically the historical ambient coordinate shell.
- codimension three does not by itself prove V_N^perp = span{1,d,d²}.
- OBS-015 remains permanent; source G1-B1B/G1-final/S-NEG/G23 stays open.
- finite-to-infinite convergence remains dormant.

## Current post-green records

- `PARITY_POST_GREEN_RESET_2026_09_03.md`
- `PARITY_FLOW_GEOMETRY_POST_GREEN_RESET_2026_09_03.md`
- `../../RESEARCH_LEADS_POST_102_DELTA.md`
- `../../RESEARCH_LEADS_POST_103_DELTA.md`

**RH remains OPEN.**
