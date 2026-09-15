# R003 — CCM / finite Weil bridge

Status: **ACTIVE. THEOREM AUTHORITY THROUGH PR #184. LATEST RESEARCH EVIDENCE THROUGH PR #180. CURRENT FRONTIER = FB-05 REMAINDER-DRIFT FALSIFICATION + PRODUCTION DERIVATIVE WITNESSES. RH OPEN.**

## Authority split

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

CONTROL AUTHORITY
control-plane semantic anchor = PR #117
selected formal first break = E4A4-SCHUR-FB-05
RH = OPEN
```

## Closed theorem ladder

```text
finite canonical obstruction / Euclidean wall                   PROVED / #94-#98
N-flow + parity + first-bad + Schur/secular                     PROVED / #100-#128
source-explicit cross-parity transfer                            PROVED / #129
exact canonical source-moment decomposition                      PROVED / #131
zero-shift source transport / absolute energy / determinant      PROVED / #134-#137
regular selected first-bad endpoint                              PROVED / #140-#150
retained first-bad + exact pole-prime discrepancy                PROVED / #153
legal Riesz engine + parity/even jets                            PROVED / #155
complex production D transport + complete Riesz 6/even 8         PROVED / #157
retained transformed negativity                                  PROVED / #157
moment-prefix odd jets + signed Riesz boundary                    PROVED / #159
same-state shifted Riesz x cross-parity source                   PROVED / #161
mixed quadratic-normal jet x Riesz boundary                      PROVED / #163
generic real 2x2 Schur-envelope derivative                       PROVED / #182
H1 contact determinant/pivot orientation equivalence             PROVED / #182
complex-Hermitian 2x2 Schur calculus                             PROVED / #184
full frozen parity log-cover production family                   PROVED / #184
fixed-cell bridge to actual parityCompressedCanonical            PROVED / #184
N2 predecessor/canonical-shell reconstruction + orthogonality    PROVED / #184
algebraic universal-drift/remainder envelope decomposition       PROVED / #184
conditional negative orientation under remainder domination      PROVED / #184
```

## Research state through #180

The q13/N2/K3/even finite microscope has consumed the following research sequence:

```text
#165 endpoint scalar
#166 true shifted-state discriminator
#167 Q16 interval-method audit
#168 threshold moment jets / Q17 microscope
#170 theorem-aligned [W|c] Schur visibility/background split
#172 threshold-to-threshold production barrier
#174 exact q13 2x2 scalar barrier
#176 fixed-unit enclosure method acceptance
#178 complete fixed-Q physical-L derivative implementation
#180 exact-center derivative basin / Schur H1-scope audit
```

Exact #180 finite state:

```text
POINT_DERIVATIVE_BASIN_BRACKETED
MINIMUM_ORIENTED
left centers:  3/3 Delta_2' < 0
right centers: 3/3 Delta_2' > 0
SCHUR_OUT_OF_H1_SCOPE on primary nonzero-width Schur boxes
applicable_primary_count = 0
uniqueness_claim = false
```

No bad interval or H1-loss interval is certified.

## What #184 changes for R003

The structural Pair-A bridge is no longer merely a desired theorem shape. Lean now has the complex-Hermitian Schur calculus and the exact full frozen parity family

```text
M~(t) = -t I + R~(t)
```

on logarithmic coordinate `t`, with fixed-cell equality to the actual production family. In N2/K3 geometry the canonical predecessor and canonical cubic shell are theorem-backed and orthogonal.

The algebraic envelope derivative is theoremized as

```text
P_t' = - envelopeNormSq + remainderEnvelopeDerivative.
```

If the remainder derivative is smaller than the envelope norm square, #184 proves negative pivot orientation.

R003 therefore should not spend new cycles rediscovering the real 2x2/Hermitian algebra. The next finite question is whether the **actual production arithmetic remainder** can numerically or rigorously outrun the universal drift on the already-frozen dangerous q13/Q14 states.

## Immediate finite falsification lane

### Coordinate lock

#184 uses `t=log L`. Existing #178/#180 code differentiates in physical aperture `L`. Thus

```text
dP/dt = -E + dR/dt
```

becomes

```text
dP/dL = -E/L + dR/dL.
```

The domination condition to test with the existing backend is

```text
dR/dL < E/L
```

or equivalently

```text
L*dR/dL < E.
```

Do not compare a log-coordinate derivative directly with a physical-L derivative.

### Frozen experiment specification

Reuse the exact #180 schedule. Do not move centers or refit the basin.

For each existing frozen q13/Q14 N2/K3 state, compute or enclose separately:

```text
envelope_norm_sq = E
universal_log_drift_L = -E/L
full_pivot_derivative_L
production_remainder_drift_L
  = full_pivot_derivative_L + E/L

domination_margin_L
  = E/L - production_remainder_drift_L

normalized_ratio
  = L * production_remainder_drift_L / E
```

Required consistency check:

```text
full_pivot_derivative_L
  = universal_log_drift_L + production_remainder_drift_L.
```

The research output should classify whether the candidate domination mechanism is:

```text
DOMINATION_SIGNAL_STRONG
DOMINATION_SIGNAL_MIXED
DOMINATION_SIGNAL_FAILS
DOMINATION_SIGNAL_UNRESOLVED
```

These are research classifications only, not theorem promotion.

If the ratio reaches or exceeds 1 on a legitimate retained/frozen state, the simple remainder-domination formulation is falsified in that scope and must be revised before Lean investment.

## Formal Pair-A lane after the falsification pass

The repo already proves entrywise holomorphy of the complete frozen complex source remainder on the punctured safe strip. The next formal work should transport that existing analyticity through the exact parity projection and N2 predecessor/canonical-shell pairings.

Target scalar derivative witnesses:

```text
a_R'(t)
(Re b_R)'(t)
(Im b_R)'(t)
d_R'(t)
```

Then instantiate #184's algebraic identity as an actual production `HasDerivAt` statement. Only after this interface is theorem authority should the project attempt the source-specific bound needed for negative contact orientation.

## Finite-width H1 lane remains available

The existing #180 nonzero-width Schur boxes still stop first at H1 scope. If the remainder-drift route needs interval neighborhoods rather than exact centers, use the already-planned order:

```text
1. centered H1 recovery from point a(L0)>0 + rigorous a'(I)
2. inside recovered H1, retry the Schur derivative box
3. if still unresolved, add Delta_2'' / centered propagation
4. interval Newton/Krawczyk only after signed neighborhoods
```

Do not revive raw derivative-box subdivision with only more precision/depth.

## Normalization / representation firewalls

- the q13 research integer shell generator spans the same one-dimensional shell as Lean's canonical cubic shell but is not theorem-identified at the same magnitude;
- production is complex Hermitian; do not substitute real `b^2/a` for `|b|^2/a` outside a theorem-backed specialization;
- `t=log L` and physical `L` derivatives differ by a factor of `L`;
- analyticity of the remainder does not imply the needed magnitude bound;
- global Schur monotonicity remains quarantined;
- independent channel Schur pivots cannot be summed because the Schur map is nonlinear;
- finite Arb output is evidence only in its encoded finite scope;
- q13/N2/K3 finite evidence does not automatically generalize to arbitrary retained first-bad states.

## Current open route obligations

```text
actual N2 production remainder scalar derivative witnesses
actual production HasDerivAt Schur log-drift identity
production remainder/contact-orientation domination bound
same-state first-bad opposing contact orientation
centered finite-width H1 on the frozen #180 boxes
q13 whole-cell sign/contact/nonvanishing
sourceMoment <-> M4 rigidity
endpoint-scalar global sign/nonvanishing
simultaneous parity bad exclusion
odd-selected closure
independent contradiction-producing arithmetic restriction
negative-root exclusion
terminal zeta/Mathlib seam
RiemannHypothesis
```

Newest synthesis:
`../../RESEARCH_LEADS_POST_184_HERMITIAN_LOG_DRIFT_REMAINDER_DOMINATION_DELTA.md`.

**RH remains OPEN.**