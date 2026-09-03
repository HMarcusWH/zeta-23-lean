# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

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

## Current theorem-backed internal route

~~~text
F1 finite canonical negative obstruction                    PROVED
K0-F1 constrained algebra / Hermitianity                    PROVED
K0-F1E Euclidean constrained sector                         PROVED
N-FLOW fixed-L persistent negative tail                     PROVED / #100
PARITY reversal symmetry / even commutator collapse         PROVED / #102
PARITY-FLOW direct split / D-equivalence                    PROVED / #103
PARITY-BAD least bad size + 1D successor shell              PROVED / #105
FIRST-BAD-SPECTRUM constrained compression                  PROVED / #107
compressed/self quadratic agreement                         PROVED / #107
symmetric compressed operator                               PROVED / #107
negative constrained Rayleigh eigenmode                     PROVED / #107
successor-level predecessor nonnegativity                   PROVED / #107
negative eigenmode not inherited                            PROVED / #107
off-line zero -> first-bad spectral endpoint                PROVED / #107

nonzero orthogonal shell projection                         DERIVED / OPEN FORMALIZATION
negative index one / unique negative eigenline              DERIVED / OPEN FORMALIZATION
normal-space / Schur / KKT rigidity                         OPEN
RH                                                           OPEN
~~~

## Current execution priority

1. Internalize the centered predecessor image as a submodule of the successor parity subtype.
2. Prove its intrinsic orthogonal complement has complex dimension one.
3. Upgrade #107 `not inherited` to an explicit nonzero orthogonal shell projection.
4. Prove negative index exactly one / unique negative eigenline if the Mathlib route stays cheap.
5. Theorem-lock parity-specific normal spaces: even `span{1,d²}`; odd `span{d}`.
6. Derive the parity KKT residual for the #107 negative eigenmode.
7. Derive the safe shifted Schur/Feshbach identity using `A - lam I`, `lam < 0`.
8. Compose the even KKT branch with the proved D/displacement commutator collapse and inspect
   the projected `d³` defect.

Uniqueness is useful but no longer a prerequisite for KKT/Schur: #107 already supplies a specific
negative eigenmode with `lam < 0` and a non-inherited component.

The source-faithful G1-B1B/G1-final/S-NEG/G23 lane remains parallel.

**RH remains OPEN.**
