# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

## Current authority snapshot

~~~text
theorem-state anchor = PR #105 merge 5e19483c905c07cfe9fef0a97f834004e77b5fb9
validated theorem head = 100fb03cccd44d1c09dadfc41cd104ba753308ee
validated synthetic merge = 4411f6a5a5c679795e043968db70f44922c2a468
theorem tree = 84ed44aaf5ff014a9352901ff1a1a31a29809b6e
theorem-bearing merged through = PR #105
RHRC #706 = SUCCESS
Permansson #479 = SUCCESS
axioms = [propext, Classical.choice, Quot.sound]
sorryAx = absent
date = 2026-09-03
RH = OPEN
~~~

The exact synthetic-merge tree checked by CI is the same tree merged on main.

## Current RH-directed theorem ladder

~~~text
off-line zeta zero
  -> compact C² pole-neutral negative W test                       PROVED
  -> strict aperture + legal finite approximation                 PROVED
  -> canonical finite negative obstruction                        PROVED / #94
  -> constrained algebra / Hermitianity / displacement            PROVED / #96
  -> Euclidean constrained sector / exact dimensions              PROVED / #98
  -> exact centered N-flow / fixed-L negative tail                PROVED / #100
  -> exact reversal symmetry / even commutator collapse           PROVED / #102
  -> direct parity geometry / D : V+ ≃ V-                         PROVED / #103
  -> D_M E = E D_N                                                PROVED / #105
  -> exact quadratic parity split q(u)=q(u+)+q(u-)                PROVED / #105
  -> negative witness -> one bad parity                           PROVED / #105
  -> fixed parity bad tail                                        PROVED / #105
  -> least bad parity size N*>=2                                  PROVED / #105
  -> predecessor parity sector nonnegative                        PROVED / #105
  -> exact Euclidean successor parity shell has finrank 1         PROVED / #105

NEXT
  parity-constrained Euclidean compression
  exact compressed/self quadratic agreement
  symmetric compressed operator
  negative constrained Rayleigh eigenmode
  first-bad unique negative eigenline
  nonzero 1D-shell component of every negative eigenmode

THEN
  parity-specific normal spaces
  scalar Schur/Feshbach equation
  parity KKT residual
  D/displacement rigidity

PARALLEL
  source-faithful G1-B1B -> G1-final -> S-NEG -> G23

RH                                                                 OPEN
~~~

## What #105 changed

`Zeta23/CCM/ParityBadness.lean` is now in the validated `Zeta23.CCM` import closure. The previous staged-source warning is retired as a current-state description; OBS-018 remains a permanent validation firewall.

The key endpoint is now theorem-backed:

[
	ext{off-line zero}
Rightarrow
exists L>0,p,N_*:
operatorname{ParityBad}(p,L,N_*),
]

with one fixed parity bad for all larger sizes, a least bad size (N_*ge2), a nonnegative predecessor parity sector, and a one-complex-dimensional Euclidean successor shell.

The next phase is no longer “find a finite bad witness.” It is “classify the only way the first parity-resolved bad state can occur.”

## Permanent firewalls

- D-equivalence is algebraic, not unitary.
- D commuting with N-flow does not imply D maps orthogonal shells to orthogonal shells.
- least badness is for the selected parity only.
- one-dimensional shell growth does not itself contradict negativity.
- no compressed operator, negative eigenmode, KKT equation, positivity theorem, finite-to-infinite theorem, or RH theorem is proved yet.

## Living research records

- `research/RHRC/CURRENT_RESEARCH_PLAN.md`
- `research/RHRC/RESEARCH_LEADS.md`
- `research/RHRC/RESEARCH_LEADS_POST_105_DELTA.md`
- `research/RHRC/routes/R003_ccm_bridge/PARITY_BAD_POST_GREEN_RESET_2026_09_03.md`
- `research/RHRC/CLAIM_REGISTRY.json`
- `research/RHRC/R003_PROMOTED_BINDINGS.json`

**RH remains OPEN.**
