# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

## Current authority snapshot

Live GitHub head + exact Lean/compiler/CI evidence are authoritative dynamically.

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
selected first break = E4A4-SCHUR-FB-05
RH = OPEN
```

The theorem, research and control anchors are intentionally separate.

## Current theorem ladder

```text
off-line zero -> legal finite canonical negative obstruction            PROVED
first-bad / parity / Schur / secular machinery                          PROVED
source-explicit cross-parity transfer                                   PROVED / #129
exact canonical source-moment decomposition                             PROVED / #131
zero-shift source transport / absolute source energy / determinant      PROVED / #134-#137
regular selected first-bad endpoint                                     PROVED / #140-#150
retained first-bad + exact pole-prime discrepancy                       PROVED / #153
legal generic Riesz smoothing + parity/even source jets                 PROVED / #155
complex production D transport + exact complete Riesz 6/even 8          PROVED / #157
retained transformed negativity + off-line-zero R6 wrapper              PROVED / #157
general moment-prefix odd-jet law                                       PROVED / #159
exact seventh / even ninth leading-moment self-energy jets              PROVED / #159
generic signed complete-channel Riesz boundary recurrence               PROVED / #159
same-state shifted Riesz x cross-parity source composition              PROVED / #161
odd-good -> nonzero exact production source moment                      PROVED / #161
mixed quadratic-normal seventh source jet -> M4                         PROVED / #163
finite-prime sampling of the same mixed source observable               PROVED / #163
mixed-jet squared Riesz-8/Riesz-9 boundary coupling                     PROVED / #163
retained mixed-jet/Riesz specialization                                 PROVED / #163
generic real 2x2 Schur-envelope derivative calculus                     PROVED / #182
H1 contact determinant/pivot derivative orientation equivalence         PROVED / #182
complex-Hermitian 2x2 Schur calculus                                    PROVED / #184
full frozen parity production family M~(t)=-tI+R~(t)                    PROVED / #184
exact fixed-cell bridge to parityCompressedCanonical                    PROVED / #184
N2 predecessor/canonical-cubic-shell reconstruction and orthogonality   PROVED / #184
algebraic P_t'=-envelopeNormSq+remainderEnvelopeDerivative              PROVED / #184
remainder domination -> negative pivot orientation                      PROVED / #184

source-moment / M4 canonical-state rigidity                             OPEN
endpoint-scalar global sign/nonvanishing                                OPEN
actual production remainder scalar derivative witnesses                OPEN
actual production HasDerivAt Schur log-drift identity                  OPEN
source-specific production remainder domination/contact sign           OPEN
first-bad contact existence/orientation composition                     OPEN
q13 finite-width H1 / whole-cell sign-contact classification            OPEN / ACTIVE
simultaneous even/odd bad exclusion                                     OPEN
odd-selected first-bad branch closure                                   OPEN
negative-root exclusion                                                 OPEN
outside-strip/trivial-zero seam + Mathlib RH wrapper                    OPEN
RH                                                                      OPEN
```

## What #184 changed

PR #184 moves the contact-orientation route from a real research proxy to the actual complex-Hermitian production geometry.

For a Hermitian 2x2 block, Lean now uses the genuine correction

```text
P = d - |b|^2/a
```

and theoremizes the corresponding pivot/determinant derivative calculus, including real-component derivative theorems for the complex off-diagonal coordinate.

More importantly, #184 defines the full frozen parity production family on logarithmic coordinate `t` and proves

```text
M~(t) = -t I + R~(t)
```

with exact fixed-cell equality back to the actual `parityCompressedCanonical` family.

For the N2/K3 intrinsic predecessor/shell geometry it proves the canonical cubic shell is nonzero, the predecessor and shell reconstruct the successor, and they are orthogonal. Under the required scalar derivative data, Lean proves the exact algebraic envelope split

```text
P_t' = -envelopeNormSq + remainderEnvelopeDerivative
```

and therefore

```text
remainderEnvelopeDerivative < envelopeNormSq -> P_t' < 0.
```

This isolates all possible cancellation of the universal negative drift into the production remainder derivative.

### #184 claim firewall

#184 does **not** yet transport the already-proved complex remainder holomorphy all the way to the actual N2 real scalar derivative witnesses. It therefore does not yet give a fully instantiated production `HasDerivAt` Schur theorem or a source-specific domination inequality.

It also does not prove contact existence/uniqueness, a first-bad crossing orientation theorem, global Schur monotonicity, first-bad exclusion, negative-root exclusion or RH.

## Research progression through #180

The post-#163 finite research chain remains consumed infrastructure/evidence:

- **#165:** exact executable endpoint-scalar audit.
- **#166:** discovery aligned with the true shifted secular state.
- **#167:** Q16 whole-cell direct interval representation found dependency-limited.
- **#168:** boundary-flat threshold jets and Q17 microscope.
- **#170:** theorem-aligned `[W|c]` Schur visibility/background audit.
- **#172:** threshold-to-threshold production barrier audit; current-q entry lift sign-indefinite.
- **#174:** q13/N2/K3/even exact 2x2 scalar barrier; direct scalar interval subdivision unresolved.
- **#176:** fixed-unit value representation accepted by the frozen factor-2 width benchmark.
- **#178:** complete fixed-Q physical-`L` derivative implementation validated; raw nonzero-width derivative boxes unresolved.
- **#180:** all six frozen primary exact-center derivative balls are minimum-oriented; nonzero-width Schur boxes are `SCHUR_OUT_OF_H1_SCOPE` with zero applicable primaries.

Exact #180 point state:

```text
POINT_DERIVATIVE_BASIN_BRACKETED
MINIMUM_ORIENTED
left centers:  3/3 Delta_2' < 0
right centers: 3/3 Delta_2' > 0
uniqueness_claim = false
```

## Current active path — FB-05

The active strategy is a **same-state incompatibility** search rather than a requirement for one RH-sized miracle lemma.

### Immediate finite falsification lane

#184 is written in `t=log L`, while the existing R003 derivative backend differentiates with respect to physical aperture `L`. Therefore

```text
dP/dt = -E + dR/dt
```

must be compared to the R003 form

```text
dP/dL = -E/L + dR/dL.
```

The next research test should reuse the exact frozen #180 q13/Q14 schedule and separately report

```text
universal_log_drift_L = -E/L
production_remainder_drift_L
full_pivot_derivative_L
domination_margin_L = E/L - production_remainder_drift_L
normalized_ratio = L * production_remainder_drift_L / E
```

with an exact arithmetic/enclosure cross-check that the two components reconstruct the full derivative.

This test should be run **before** theorem investment in the source-specific domination bound.

### Formal Pair-A lane

The analytic infrastructure already proves entrywise holomorphy of the complete frozen complex source remainder. The next theorem bridge should transport that through the exact parity projection and N2 predecessor/canonical-shell pairings to produce actual real derivative witnesses for

```text
a_R, Re b_R, Im b_R, d_R.
```

Those witnesses then instantiate #184's algebraic identity as an actual production `HasDerivAt` Schur theorem. Only after that should the project attempt a source-specific contact-local remainder domination theorem.

## Production / coordinate firewalls

- the q13 research integer shell generator spans the same one-dimensional shell as Lean's canonical cubic shell but is not theorem-identified with the same magnitude;
- #184 closes the complex-Hermitian/log-cover algebraic interface, not the source-specific derivative magnitude bound;
- `t=log L` derivatives and physical-`L` derivatives differ by the factor `L` and must not be mixed;
- analyticity does not imply a useful domination bound;
- do not silently discard moving-optimizer/envelope terms;
- global minimizing-Schur monotonicity remains quarantined;
- q13/N2/K3 finite evidence does not automatically generalize to arbitrary retained first-bad states.

## Documentation authority

Current living state is maintained in:

- `research/RHRC/CURRENT_RESEARCH_PLAN.md`;
- `research/RHRC/RESEARCH_LEADS.md`;
- `research/RHRC/RESEARCH_LEADS_POST_184_HERMITIAN_LOG_DRIFT_REMAINDER_DOMINATION_DELTA.md`;
- `research/RHRC/FB05_INCOMPATIBILITY_PROGRAM.md`;
- `research/RHRC/DOCUMENTATION_AUTHORITY.md`;
- `research/RHRC/VALIDATION_PROTOCOL.md`;
- `research/RHRC/routes/R003_ccm_bridge/README.md`;
- `research/RHRC/control_v2/README.md`.

Older dated deltas, external reviews and countermodel records remain historical evidence and are not rewritten to look current.

## Permanent firewalls

- RH remains OPEN.
- theorem authority is compiler evidence, not PR title or prose.
- research green is not theorem authority.
- finite Arb certification is not a global theorem.
- transformed negativity is not a contradiction.
- `UNRESOLVED` is not sign evidence.
- global aperture/Schur monotonicity remains quarantined.
- #184's algebraic log-drift split is not a source-specific arithmetic domination theorem.
- determinant and pivot minima are distinct optimization targets.
- simultaneous parity badness and odd-selected coverage remain open.
- negative-root exclusion is not the terminal Mathlib `RiemannHypothesis` statement without the final seam.

**RH remains OPEN.**