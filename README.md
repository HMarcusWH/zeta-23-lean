# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

## Current authority snapshot

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

PR #107 is merged. CI checked synthetic merge `19cd290510fe4fb1d253522c29644ff3e4563c03`,
and merged `main` has the identical theorem tree `719b45162fd0814581759661f12eab16c46e1201`.

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
  -> fixed parity bad tail + least bad size                       PROVED / #105
  -> predecessor parity sector nonnegative                        PROVED / #105
  -> exact Euclidean successor parity shell finrank 1             PROVED / #105
  -> parity-constrained Euclidean compression                     PROVED / #107
  -> exact compressed/self quadratic agreement                    PROVED / #107
  -> symmetric compressed canonical operator                      PROVED / #107
  -> ParityBad -> genuine negative Rayleigh eigenmode             PROVED / #107
  -> predecessor nonnegativity transported to successor matrix    PROVED / #107
  -> negative first-bad eigenmode is not inherited                PROVED / #107
  -> off-line zero -> first-bad negative spectral endpoint        PROVED / #107

NOW — FIRST-BAD-RIGIDITY
  intrinsic predecessor subspace inside successor parity Hilbert space
  explicit nonzero orthogonal shell projection
  negative index exactly one / unique negative eigenline          DERIVED / OPEN FORMALIZATION
  parity-specific normal spaces
  parity KKT residual
  shifted Schur/Feshbach equation
  D/displacement rigidity

PARALLEL
  source-faithful G1-B1B -> G1-final -> S-NEG -> G23

RH                                                                 OPEN
~~~

## What #107 changed

Lean now defines the parity-constrained orthogonal compression of `canonicalSourceMatrix`, proves
exact compressed/self quadratic agreement and symmetry, and converts `ParityBad` into a genuine
negative eigenpair. At the least bad size, predecessor nonnegativity is transported from size `N`
to the exact centered image inside size `N+1`; the proof does not identify those matrices.

The ExceptionalZero endpoint now proves: fixed `L>0`, fixed parity, least bad successor,
`lam<0`, `v!=0`, `Tv=lam v`, predecessor nonnegativity, `v` not inherited from the predecessor,
and a one-complex-dimensional successor parity shell.

## Immediate derived consequences

**DERIVED / not yet separately formalized:**
- the #107 negative eigenmode has nonzero projection to the one-dimensional successor shell;
- the first-bad compressed operator has negative index exactly one, hence one negative eigenline.

## Permanent firewalls

- D-equivalence is algebraic, not unitary.
- `v ∉ predecessorImage` does not mean `v` lies purely in the shell.
- the successor shell is not proved invariant.
- use `A - lam I` for `lam < 0`; never assume `A⁻¹` for the semidefinite predecessor block.
- unique negative eigenline, parity normal spaces, KKT, Schur/Feshbach, positivity,
  finite-to-infinite closure and RH remain OPEN unless separately theorem-backed.

## Living research records

- `research/RHRC/CURRENT_RESEARCH_PLAN.md`
- `research/RHRC/RESEARCH_LEADS.md`
- `research/RHRC/RESEARCH_LEADS_POST_107_DELTA.md`
- `research/RHRC/routes/R003_ccm_bridge/README.md`
- `research/RHRC/CLAIM_REGISTRY.json`
- `research/RHRC/R003_PROMOTED_BINDINGS.json`

**RH remains OPEN.**
