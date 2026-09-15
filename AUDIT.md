# RHRC formal audit — theorem authority through PR #184; research evidence through PR #190

> **RH remains OPEN.**

Live GitHub head + exact compiler/CI evidence outrank this prose.

## Authority split

```text
THEOREM AUTHORITY
PR #184
head  = a756494ebe7e2530715e996b9a9a341fbe07c683
merge = 6f04e94473eb112b59eeaa2c6fc6ac6cbe7fe30e
tree  = 6c77cd470809959a403b3bcc5f08d39f4076fa4c

LATEST RESEARCH EVIDENCE
PR #190
head  = 8701920b0da18ae6595ad0eee55c1f6cb291a94f
merge = f87da9fde71dd1e74419c6ae5848eee3787c27e4
tree  = af8774b65c898de221a5bf32977ccff3407a7b2d
RHRC #1096 = SUCCESS
Permansson #869 = SUCCESS

CONTROL SEMANTIC AUTHORITY
PR #117
selected first break = E4A4-SCHUR-FB-05
terminal claim = RH_OPEN
```

## Formal theorem state

No Lean theorem has been added after PR #184. The formal production-facing package still proves, in its exact scopes:

```text
Hermitian P = d - |b|^2/a
contact-local determinant/pivot derivative orientation transfer under H1
full frozen parity production family M~(t) = -t I + R~(t)
exact fixed-cell bridge to parityCompressedCanonical
N2 predecessor/canonical-shell reconstruction
canonical shell != 0
predecessor ⟂ shell
P_t' = -envelopeNormSq + remainderEnvelopeDerivative
remainderEnvelopeDerivative < envelopeNormSq -> P_t' < 0
```

Still not proved: source-specific remainder domination, contact existence/uniqueness, opposing first-bad orientation on the same state, first-bad exclusion, negative-root exclusion or RH.

## Research audit: #186 -> #190

### PR #186 — broad domination falsifier

On the exact frozen #180 Q14 panel, the physical-aperture decomposition

```text
P_L' = -E/L + R_L'
margin_L = E/L - R_L'
rho_L = L*R_L'/E
```

returned `DOMINATION_SIGNAL_MIXED`: two positive margins, four negative margins, no unresolved exact centers. The broad universal domination hypothesis therefore failed in this tested finite scope.

### PR #188 — selector audit

The frozen post-#186 audit introduced ten normalization-safe candidates. Seven were marked strong-eligible:

```text
G1_COUPLING_RATIO
P1_PARITY_LEVEL_RATIO
P2_PARITY_LOG_SLOPE_GAP
C1_PRIME_PIVOT_CONTRIBUTION
C2_ARCH_PIVOT_CONTRIBUTION
C3_POLE_PIVOT_CONTRIBUTION
C4_PRIME_VS_SMOOTH_MAGNITUDE
```

R1/R2/R3 remained diagnostic-only because their sum reconstructs a target-adjacent mechanism quantity.

### PR #189 — individual semantic independence

For every frozen candidate separately, exact rational ambient states were certified with the same candidate value and same nonboundary threshold relation but opposite target signs. Result: no individual frozen candidate determines the target sign in the audited normalized algebra.

### PR #190 — joint semantic independence

PR #190 closes the remaining composition hole. It certifies two exact rational ambient states with:

```text
identical complete seven-dimensional strong selector vector
identical nonboundary threshold signature
opposite normalized FB-05 target signs
```

The executable classifications are:

```text
JOINT_EXACT_VECTOR_SEPARABLE
JOINT_THRESHOLD_SIGNATURE_SEPARABLE
```

Since the full seven-vector is identical, every one of its `2^7 - 1 = 127` nonempty coordinate subsets is identical as well. No search over those subsets can restore information in this ambient algebra.

The positive controls `channel_sum`, `direct_full_ratio`, and `mechanism_sum` do distinguish the pair and reconstruct the target exactly, confirming that the audit still detects target-containing observations.

## Exact post-#190 limitation

#190 does **not** prove that its reflected rational pair is realizable by the canonical arithmetic CCM construction. Its module and certificate explicitly keep

```text
canonical_realizability_claimed = false
fb05_closed = false
negative_root_exclusion = false
rh_claim = false
```

Therefore the correct conclusion is not “Pair A is impossible.” It is:

```text
frozen selector composition is insufficient in the ambient normalized state space;
the missing information, if Pair A survives, must enter through canonical production realizability or another independent same-state restriction.
```

## Current post-green frontier

The next research target is a **canonical-realizability audit** of the #190 reflected twin. Actual production computes all channels and geometry from one common aperture/state. In particular the current research backend constructs

```text
scalar_shift = 2*cCorrection'(L) I
arch_signed  = -arch_direct - scalar_shift
```

so the abstract scalar/arch degrees of freedom used in #190 are not obviously independent production degrees of freedom.

The correct next experiment is layered:

```text
ambient normalized algebra
 -> four-way production channel coupling
 -> exact scalar-aperture law
 -> common archimedean derivative
 -> common Schur geometry x,E
 -> full same-L canonical source reconstruction
```

At each layer, ask whether an exact same-seven-vector/opposite-target twin can still exist. A numerical failure to find one is not a theorem; the goal is to isolate the first exact production relation that provably forbids the twin.

## Claim firewall

```text
#184 theorem package
  -/-> source-specific sign law

#186 finite falsification
  -/-> global opposite-sign theorem

#189 individual separability
  -/-> canonical arithmetic independence

#190 joint separability
  -/-> canonical realizability of the reflected pair

production arch/scalar coupling
  -/-> FB-05 closure until an exclusion theorem is actually proved
```

Global Schur monotonicity remains quarantined. Negative-root exclusion remains OPEN. The terminal zeta/Mathlib seam remains OPEN. **RH remains OPEN.**