# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

## Current authority snapshot

~~~text
theorem-state anchor = PR #103 merge c7129b1856ea03cdf8b831ae1424140f8a7d90a9
validated theorem head = af43242f55536a8170bf303b9c9558c6a0fccdcf
validated synthetic merge = 16c5ebaa6d6d7e14df853e9a0771ab5ef3b07aba
theorem tree = 56d082947fac6eb4666d0e0666e2c8bcd3c0a7e8
theorem-bearing merged through = PR #103
live GitHub main = authoritative
RH = OPEN
~~~

## Current theorem-backed internal route

~~~text
W2-A/W0/W1/W2-ZS + G1-A                                 PROVED
F0-B1A/B1B/WCONT/F0-B1C-A/B                             PROVED
strict finite sign transfer + F1                        PROVED
K0-F1 / K0-F1E constrained finite + Euclidean algebra   PROVED
N-FLOW exact centered nesting + fixed-L negative tail   PROVED / #100
PARITY reversal/moment/matrix symmetry                   PROVED / #102
PARITY even constrained commutator collapse              PROVED / #102
PARITY direct even/odd constrained decomposition         PROVED / #103
PARITY D-induced even/odd linear equivalence             PROVED / #103
PARITY exact finrank N-1 / N-1                          PROVED / #103
PARITY-preserving Euclidean N-flow                       PROVED / #103

global first-bad N                                       DERIVED
general negative witness -> fixed negative parity        DERIVED / OPEN FORMALIZATION
ParityBad/least-parity-bad/1D-shell source               STAGED / NOT VALIDATED
K0-F1F constrained spectral compression                  OPEN
normal-space / KKT / scalar secular rigidity             OPEN
RH                                                        OPEN
~~~

## Validated-import-closure firewall

A merged Lean file is not automatically theorem authority. `ParityBadness.lean` exists on main but is not imported by `Zeta23.CCM`, so its declarations remain **STAGED / NOT VALIDATED**. See `VALIDATION_PROTOCOL.md` and OBS-018.

## Current execution priority

1. Import and compile `ParityBadness.lean`.
2. Theorem-lock `D_M E_{N,M} = E_{N,M} D_N`.
3. Theorem-lock exact quadratic parity splitting.
4. Extract one fixed negative parity from the #100 negative witness and propagate it by exact N-flow.
5. Take the least bad parity size and validate the one-dimensional successor parity shell.
6. Build constrained orthogonal compression and extract a negative constrained eigenmode.
7. Prove the exact normal-space identity, then KKT and scalar Schur/Feshbach rigidity.
8. Open aperture/prime-event first crossing only if fixed-L finite rigidity still needs arithmetic closure.

## Source route

S-GEOM/G1-B1A is proved. S-IFACE/G1-B1B, G1-final, S-NEG and G23 remain open as an alternate/cross-check route.

## Current records

- `RESEARCH_LEADS_POST_102_DELTA.md`
- `RESEARCH_LEADS_POST_103_DELTA.md`
- `routes/R003_ccm_bridge/PARITY_POST_GREEN_RESET_2026_09_03.md`
- `routes/R003_ccm_bridge/PARITY_FLOW_GEOMETRY_POST_GREEN_RESET_2026_09_03.md`

External v2.0 should be written against the post-#103 validated repository state.

**RH remains OPEN.**
