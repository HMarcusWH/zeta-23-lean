# R003 — CCM / finite Weil bridge

Status: **ACTIVE. THEOREM AUTHORITY THROUGH PR #184. LATEST RESEARCH EVIDENCE THROUGH PR #186. CURRENT FRONTIER = FB-05 MIXED-SPLIT DISCRIMINATOR + PRODUCTION DERIVATIVE WITNESSES. RH OPEN.**

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
merged research PR = #186
validated research head = 7d277a99437d98fdb7c831f25a130eac07f1b3af
merged research commit = 0494658a87d29eeb2124aa16232c264c21d23c18
RHRC #1091 = SUCCESS
Permansson #864 = SUCCESS
research disposition = DOMINATION_SIGNAL_MIXED

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

## Research state through #186

The q13/N2/K3/even finite microscope has consumed:

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
#186 coordinate-correct production remainder-drift falsifier
```

Exact #180 finite state remains part of the ancestry:

```text
POINT_DERIVATIVE_BASIN_BRACKETED
MINIMUM_ORIENTED
left centers:  3/3 Delta_2' < 0
right centers: 3/3 Delta_2' > 0
SCHUR_OUT_OF_H1_SCOPE on primary nonzero-width Schur boxes
applicable_primary_count = 0
uniqueness_claim = false
```

#186 then decomposes the physical-L Schur derivative on the exact same frozen schedule:

```text
P_L' = -E/L + R_L'
margin_L = E/L - R_L'
rho_L = L*R_L'/E
```

The primary exact-center result is:

```text
DOMINATION_SIGNAL_MIXED

positive margin:
  det_left_o2^-10_r2^-13
  det_left_o2^-13_r2^-16

negative margin:
  det_right_o2^-10_r2^-13
  det_right_o2^-13_r2^-16
  det_left_o2^-16_r2^-19
  det_right_o2^-16_r2^-19

unresolved: none
finite-width scope: FINITE_WIDTH_OUT_OF_H1_SCOPE
```

This is a green falsification result. It means the simple universal source-remainder domination hypothesis is false on the tested frozen scope. It does not invalidate #184 and is not a theorem about arbitrary retained states.

## What #184 still gives R003

The structural Pair-A bridge remains theorem-backed. Lean has the complex-Hermitian Schur calculus and exact frozen parity family

```text
M~(t) = -t I + R~(t)
```

on logarithmic coordinate `t`, with fixed-cell equality to actual production. In N2/K3 geometry the canonical predecessor and canonical cubic shell are theorem-backed and orthogonal.

The algebraic envelope derivative is

```text
P_t' = - envelopeNormSq + remainderEnvelopeDerivative.
```

If the remainder derivative is smaller than the envelope norm square at a state satisfying the theorem hypotheses, #184 proves negative pivot orientation there.

What #186 removes is the expectation that this inequality holds uniformly on the dangerous finite schedule without an additional canonical condition.

## Current finite research lane — explain the mixed split

Do not move the #186 centers or fit a new basin. Use the frozen schedule as a fixed falsification panel.

Compare the two positive-margin states against the four negative-margin states using quantities with an existing canonical/theorem route, such as:

```text
E
R_L'
rho_L
P_L'
a, |b|, d
predecessor/shell norm balance
location inside the fixed-Q cell
position relative to the #180 minimum-oriented basin
same-Q ancestry/parity controls
```

The target is not “find any separator of six points.” The target is a mathematically meaningful condition that could plausibly specialize a future contact-local theorem.

Reject a proposed discriminator if it:

- merely re-encodes margin sign or successor positivity;
- depends on arbitrary normalization;
- fails the inherited control states;
- requires finite-width H1 where H1 is not certified;
- has no route from sampled side points to the actual first-bad/contact state.

## Formal lane — production derivative witnesses

The repo already proves entrywise holomorphy of the complete frozen complex source remainder on the punctured safe strip. A useful interface theorem can still transport this through the exact parity projection and N2 predecessor/canonical-shell pairings.

Target scalar derivative witnesses:

```text
a_R'(t)
(Re b_R)'(t)
(Im b_R)'(t)
d_R'(t)
```

Then instantiate #184's algebraic identity as an actual production `HasDerivAt` statement.

After #186 this work is infrastructure. It must not be interpreted as evidence that a universal remainder-domination inequality is true.

## Coordinate lock

#184 uses `t=log L`:

```text
dP/dt = -E + dR/dt.
```

#178/#180/#186 use physical aperture `L`:

```text
dP/dL = -E/L + dR/dL.
```

The #186 test correctly used `dR/dL < E/L`, equivalently `L*dR/dL < E`. Do not compare derivatives across coordinates without the factor of `L`.

## Finite-width H1 lane remains available

The #186 exact centers are H1-certified for the primary point calculation, but the inherited nonzero-width primary boxes remain outside H1 scope. If a new local discriminator needs neighborhoods:

```text
1. centered H1 recovery from point a(L0)>0 + rigorous a'(I)
2. inside recovered H1, retry the relevant Schur/remainder quantity
3. if still unresolved, add second-derivative centered propagation
4. interval Newton/Krawczyk only after signed neighborhoods
```

Do not revive raw subdivision with only more precision/depth.

## Normalization / representation firewalls

- the q13 research integer shell generator spans the same one-dimensional shell as Lean's canonical cubic shell but is not theorem-identified at the same magnitude;
- production is complex Hermitian; do not substitute real `b^2/a` for `|b|^2/a` outside a theorem-backed specialization;
- `t=log L` and physical `L` derivatives differ by a factor of `L`;
- #186 mixed finite evidence is not a general sign theorem;
- finite-width statements require certified H1;
- global Schur monotonicity remains quarantined;
- independent channel Schur pivots cannot be summed because the Schur map is nonlinear;
- q13/N2/K3 finite evidence does not automatically generalize to arbitrary retained first-bad states.

## Current open route obligations

```text
mixed-split canonical discriminator on the frozen #186 states
actual N2 production remainder scalar derivative witnesses
actual production HasDerivAt Schur log-drift identity
any valid narrowed contact-local orientation law
same-state first-bad opposing contact orientation
centered finite-width H1 on the frozen #180/#186 boxes
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
`../../RESEARCH_LEADS_POST_186_REMAINDER_DRIFT_MIXED_DELTA.md`.

**RH remains OPEN.**
