# RHRC current research plan

> **Claim firewall: RH remains OPEN.**
>
> Live GitHub/compiler/CI evidence is authoritative. A documentation-only merge may advance main without changing the theorem-state anchor below.

## Current theorem-state anchor

~~~text
theorem-bearing merge through = PR #103
final validated head = af43242f55536a8170bf303b9c9558c6a0fccdcf
synthetic merge tested = 16c5ebaa6d6d7e14df853e9a0771ab5ef3b07aba
merge = c7129b1856ea03cdf8b831ae1424140f8a7d90a9
theorem tree = 56d082947fac6eb4666d0e0666e2c8bcd3c0a7e8
RHRC #704 = SUCCESS
Permansson #477 = SUCCESS
axioms = [propext, Classical.choice, Quot.sound]
sorryAx = absent
date = 2026-09-03
RH = OPEN
~~~

## One-screen frontier

~~~text
DONE
  W2-A / W0 / W1 / W2-ZS
  G1-A
  F0-B1A/B1B/WCONT/F0-B1C-A/B
  strict finite sign transfer
  F1 canonical finite negative obstruction
  K0-F1 constrained algebra / Hermitianity / displacement
  K0-F1E exact rank 2*N-2 + Euclidean constrained sector
  N-FLOW exact centered embedding / principal-block nesting
  N-FLOW Euclidean isometric constrained flow
  N-FLOW off-line zero -> fixed-L negative constrained tail
  PARITY centered-index reversal / embedding compatibility
  PARITY moment parity / matrix reversal invariance
  PARITY displacementVector odd / even commutator collapse
  PARITY-FLOW V_N = V_N^+ direct-sum V_N^-
  PARITY-FLOW D : V_N^+ ≃ₗ[ℂ] V_N^-
  PARITY-FLOW exact finrank V_N^± = N-1
  PARITY-FLOW Euclidean parity-preserving N-flow

NOW
  import + compile ParityBadness.lean
  theorem-lock D / centered-N-flow compatibility
  theorem-lock exact quadratic parity splitting
  off-line zero -> one fixed negative parity
  fixed parity badness persistence
  least bad parity size
  exact one-dimensional parity successor shell

THEN
  constrained orthogonal compression
  negative constrained Rayleigh/eigenmode
  exact V_N^perp = span_C {1,d,d²}
  parity-resolved KKT residual
  scalar first-bad Schur/Feshbach equation
  D/displacement/Krylov/Hankel composition

IF NEEDED
  K1 aperture flow / prime-event first crossing

PARALLEL SOURCE
  G1-B1B -> G1-final -> S-NEG -> G23

RH OPEN
~~~

## Exact #100 -> #103 state transition

PR #100 turns one finite Euclidean negative direction into a fixed-aperture negative constrained tail under exact centered N-flow.

PR #102 proves the reversal chassis and exact even-channel commutator collapse.

PR #103 proves the constrained parity decomposition and, more strongly,

~~~text
D : V_N^+ ≃ₗ[ℂ] V_N^-.
~~~

The proof is structural. D has one ambient zero-index kernel; boundary-flat moment zero kills the remaining central coefficient when D u=0. Conversely, an odd vector has an explicit even primitive obtained by division by the noncentral centered index plus one central coefficient chosen to restore moment zero.

Therefore, for N>=1, both parity sectors have exact finrank N-1. Their Euclidean copies have the same dimensions and exact centered Euclidean extension preserves each sector.

## Derived but not yet theorem-locked

#100 gives global badness persistence and therefore a least global bad size when badness exists.

Because #102 makes M commute with reversal, the next theorem should prove exact quadratic splitting

~~~text
q(u) = q(u_+) + q(u_-).
~~~

Then q(u)<0 forces a negative parity component. Choosing that parity and applying #103 parity-preserving N-flow should yield a fixed-parity negative tail.

The staged `ParityBadness.lean` source expresses the intended persistence, least-bad and one-dimensional-shell API, but is outside the validated import closure.

## Highest-value upstream theorem

~~~text
D_M (E_{N,M} u) = E_{N,M} (D_N u).
~~~

If true, D coherently identifies nested even and odd sectors and should pair their new one-dimensional successor quotients.

Do not infer that D is unitary or that it conjugates future compressed parity operators.

## First-bad parity shell

After fixed-parity extraction, let N* be the least bad size in that parity. Minimality gives nonnegativity below N*. Exact parity dimensions leave one new complex direction at the successor step.

This is the intended entry point for a scalar constrained Schur/Feshbach equation. The negative vector need not lie purely in the shell; coupling to the retained nonnegative block is exactly what the Schur complement must encode.

## K0-F1F — constrained spectral extraction

Build the operator on the constrained subtype using orthogonal projection of `canonicalSourceMatrix.toEuclideanLin`. Prove symmetry and equality of constrained/ambient inner-self values, then extract a negative eigenmode by finite-dimensional Rayleigh theory.

Use variational monotonicity under exact isometric inclusion; do not claim literal nesting of compressed operators unless separately proved.

## KKT / normal space

Before asserting `M u = lambda u + a0*1 + a1*d + a2*d²`, prove

~~~text
V_N^perp = span_C {1,d,d²}.
~~~

Parity should then split residual channels: 1 and d² even, d odd.

## D / displacement composition

#102 proves [D,M]u=0 for even constrained u; #103 proves D : V_N^+ ≃ V_N^-.

This does not yet imply compressed parity-block intertwining because M u may leave the constrained subspace. After the exact normal-space theorem, the failure of intertwining must pass through a small parity-resolved normal space. That is a high-value rigidity target.

## Source and deferred lanes

- G1-B1B/G1-final/S-NEG/G23 remains independent;
- DR-010 remains dead;
- R002/Bombieri remain comparator lanes;
- finite-to-infinite convergence remains dormant;
- K1 aperture/prime-event flow remains deferred unless fixed-L finite rigidity stalls.

## Validation firewall

A merged Lean file is not theorem authority unless it lies in the exact compiler-tested import/build closure or was separately built by an authoritative gate. `ParityBadness.lean` is the current example. See OBS-018 and `VALIDATION_PROTOCOL.md`.

**RH remains OPEN.**
