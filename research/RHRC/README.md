# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

## Current authority snapshot

```text
THEOREM AUTHORITY
latest theorem-bearing PR = #184
validated theorem head = a756494ebe7e2530715e996b9a9a341fbe07c683
merged theorem commit = 6f04e94473eb112b59eeaa2c6fc6ac6cbe7fe30e
validated theorem tree = 6c77cd470809959a403b3bcc5f08d39f4076fa4c
RHRC #1089 = SUCCESS
Permansson #862 = SUCCESS

LATEST RESEARCH-EVIDENCE ANCHOR
merged research PR = #180
validated research head = a87469da9e611b53ae400cb4b18ce4afeb94e6d2
merged research commit = 93ea3df51f2671e316197c1530ea504dee76e821
research tree = 8199cdc543f1b761c70466dfd602c143a277e6a2
RHRC #1077 = SUCCESS
Lean #837 = SUCCESS
Permansson #850 = SUCCESS

CONTROL SEMANTIC AUTHORITY
PR #117 merge = 19346f4c00d13bf33db95cbe5325233f86e54c12
selected formal first break = E4A4-SCHUR-FB-05
RH = OPEN
```

## Theorem-backed route

```text
finite negative obstruction / first-bad / Schur machinery            PROVED
source-explicit cross-parity transfer                                 PROVED / #129
exact canonical source-moment decomposition                           PROVED / #131
zero-shift transport / absolute energy / determinant                  PROVED / #134-#137
regular selected first bad                                            PROVED / #140-#150
retained certificate + exact pole-prime discrepancy                   PROVED / #153
legal generic Riesz smoothing + source parity/even jets               PROVED / #155
complex production transport + exact complete Riesz 6/even 8          PROVED / #157
retained transformed negativity + ExceptionalZero R6 wrapper          PROVED / #157
general moment-prefix odd-jet law                                     PROVED / #159
same-state shifted Riesz x cross-parity source composition            PROVED / #161
mixed quadratic-normal seventh source jet -> M4                       PROVED / #163
finite-prime sampling of the same mixed source observable             PROVED / #163
mixed-jet squared Riesz-8/Riesz-9 boundary coupling                   PROVED / #163
generic real 2x2 Schur-envelope derivative                            PROVED / #182
H1 contact determinant/pivot orientation equivalence                  PROVED / #182
complex-Hermitian 2x2 Schur calculus                                  PROVED / #184
full frozen parity family M~(t)=-tI+R~(t)                             PROVED / #184
fixed-cell equality with actual production                            PROVED / #184
N2 predecessor/canonical-shell reconstruction + orthogonality         PROVED / #184
algebraic universal-drift/remainder envelope split                    PROVED / #184
remainder domination -> negative pivot orientation                    PROVED / #184

source-moment / M4 global rigidity                                    OPEN
endpoint-scalar global sign/nonvanishing                              OPEN
actual production remainder scalar derivative witnesses              OPEN
actual production HasDerivAt Schur log-drift identity                OPEN
production remainder/contact-orientation domination bound             OPEN
same-state first-bad contact orientation composition                  OPEN
q13 finite-width H1 / whole-cell sign-contact classification          OPEN / ACTIVE
simultaneous even/odd bad exclusion                                   OPEN
odd-selected branch closure                                           OPEN
negative-root exclusion                                               OPEN
terminal zeta/Mathlib seam                                            OPEN
RH                                                                    OPEN
```

## What #184 changes

The production/Hermitian interface is no longer open. PR #184 moves the contact route from the generic real #182 calculus to the actual complex-Hermitian production geometry and logarithmic cover.

Lean now proves, in the exact stated scopes,

```text
P = d - |b|^2/a
M~(t) = -t I + R~(t)
P_t' = -envelopeNormSq + remainderEnvelopeDerivative
```

along with the exact fixed-cell bridge to `parityCompressedCanonical`, N2 predecessor/canonical-cubic-shell reconstruction and orthogonality, and the conditional implication

```text
remainderEnvelopeDerivative < envelopeNormSq -> P_t' < 0.
```

The remaining source-specific gap is not the algebraic shape of the law. It is the actual remainder-coordinate differentiation and then a quantitative domination theorem.

#184 does not prove contact existence/uniqueness, source-specific domination, first-bad exclusion, negative-root exclusion or RH.

## Research state through #180

The q13/N2/K3/even finite microscope has validated value and derivative infrastructure. #180 gives exact-center orientation:

```text
POINT_DERIVATIVE_BASIN_BRACKETED
MINIMUM_ORIENTED
left centers:  3/3 Delta_2' < 0
right centers: 3/3 Delta_2' > 0
```

but the nonzero-width primary Schur boxes are

```text
SCHUR_OUT_OF_H1_SCOPE
applicable_primary_count = 0.
```

So #180 does not prove finite-width Schur sign recovery or width gain.

## Immediate frontier — FB-05

### Finite falsification lane

The theorem and research coordinates must be matched exactly.

#184 uses `t=log L`:

```text
dP/dt = -E + dR/dt.
```

#178/#180 uses physical aperture `L`, so the exact equivalent is

```text
dP/dL = -E/L + dR/dL.
```

Reuse the frozen #180 states and report separately:

```text
E
-E/L
full pivot derivative in L
production remainder derivative in L
margin = E/L - remainder_drift_L
ratio = L*remainder_drift_L/E
```

with a consistency check that the components reconstruct the full derivative.

This falsification pass comes before theorem investment in the source-specific bound.

### Formal Pair-A lane

The repo already proves entrywise holomorphy of the complete frozen complex source remainder. The next formal bridge is therefore:

```text
complex remainder holomorphy
  -> parity-compressed scalar analyticity
  -> N2 predecessor/canonical-shell pairings
  -> actual real derivative witnesses for a_R, Re b_R, Im b_R, d_R
  -> production HasDerivAt Schur identity
  -> source-specific domination
  -> same-state opposing first-bad contact orientation
```

## Production normalization / coordinate firewall

The q13 research integer shell generator spans the same one-dimensional shell as Lean's canonical cubic shell but is not theorem-identified with the same magnitude. Formal theorem work should stay on the canonical intrinsic shell.

Also:

```text
d/dt with t=log L = L * d/dL.
```

Do not compare log-coordinate and physical-L derivative magnitudes without that factor. Analyticity proves derivative existence, not a useful domination estimate.

Global Schur monotonicity remains quarantined.

## Current execution priority

1. run the post-#184 coordinate-consistent drift/remainder split on the exact frozen #180 states;
2. if the domination signal survives, theoremize the actual N2 remainder scalar derivative witnesses;
3. instantiate #184 as an actual production `HasDerivAt` Schur identity;
4. attempt a source-specific contact-local domination bound;
5. independently theoremize/identify the opposing first-bad contact orientation on the exact same retained state;
6. compose only after the same-state/same-aperture/same-parity/same-normalization firewall is satisfied;
7. preserve `RH_OPEN` until the complete negative-root and terminal seams are theorem-backed.

Newest research synthesis:
`RESEARCH_LEADS_POST_184_HERMITIAN_LOG_DRIFT_REMAINDER_DOMINATION_DELTA.md`.

**RH remains OPEN.**
