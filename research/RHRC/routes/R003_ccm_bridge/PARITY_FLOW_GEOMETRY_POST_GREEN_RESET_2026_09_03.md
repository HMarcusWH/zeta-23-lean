# PARITY-FLOW geometry post-green reset — PR #103

> **HISTORICAL SETTLEMENT.** Current authority: live Lean/CI + registries + active R003 README.
>
> **RH remains OPEN.**

## Exact checked state

~~~text
base = a434737c088ad2651491f0131b6dd6794c129f4c
validated head = af43242f55536a8170bf303b9c9558c6a0fccdcf
synthetic merge tested = 16c5ebaa6d6d7e14df853e9a0771ab5ef3b07aba
merged main = c7129b1856ea03cdf8b831ae1424140f8a7d90a9
validated/merged theorem tree = 56d082947fac6eb4666d0e0666e2c8bcd3c0a7e8
RHRC #704 = SUCCESS
Permansson #477 = SUCCESS
~~~

## Formally closed geometry

~~~text
V_N = V_N^+ direct-sum V_N^-
D : V_N^+ ≃ₗ[ℂ] V_N^-
finrank V_N^+ = N-1
finrank V_N^- = N-1
same Euclidean dimensions
exact centered Euclidean N-flow preserves parity.
~~~

D-equivalence follows from injectivity after moment zero removes the central kernel and explicit-primitive surjectivity.

## Merged but outside checked import closure

`ParityBadness.lean` was merged but not imported by `Zeta23.CCM`. Its badness, persistence, least-bad and shell declarations are not part of the proved surface.

## Route transition

Compile parity badness; prove D/N-flow compatibility and quadratic parity split; extract a fixed bad parity tail; validate least bad parity and one-dimensional shell; then move to constrained spectral compression.

## Nonclaims

No unitary parity equivalence, equal spectra, compressed intertwining, positivity, finite-to-infinite theorem or RH theorem.

**RH remains OPEN.**
