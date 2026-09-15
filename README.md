# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

## Current authority snapshot

Live GitHub head + exact Lean/compiler/CI evidence are authoritative dynamically.

```text
THEOREM AUTHORITY
latest theorem-bearing PR = #182
validated theorem head = 0c3f63cdc4774ba1a68b21d1558ea0ee860a938d
merged theorem commit = a69160d37a84049711aaff6c3d5db804583a7306
validated theorem tree = e0b260b3b3a1ed470d54c14d8c0c46b32379f3fb
RHRC #1082 = SUCCESS
Permansson #855 = SUCCESS

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

source-moment / M4 canonical-state rigidity                             OPEN
endpoint-scalar global sign/nonvanishing                                OPEN
production/Hermitian Schur-envelope bridge                              OPEN
source-specific production remainder/contact sign                      OPEN
q13 finite-width H1 / whole-cell sign-contact classification            OPEN / ACTIVE
simultaneous even/odd bad exclusion                                     OPEN
odd-selected first-bad branch closure                                   OPEN
negative-root exclusion                                                 OPEN
outside-strip/trivial-zero seam + Mathlib RH wrapper                    OPEN
RH                                                                      OPEN
```

## What #182 changed

PR #182 adds `Zeta23/CCM/SchurEnvelopeDerivative.lean` to the aggregate CCM build. For the generic real block

```text
H = [[a,b],[b,d]]
P = d - b^2/a
Delta_2 = a*d - b^2
```

Lean proves

```text
Delta_2 = a P
P' = d' - 2*(b/a)*b' + (b/a)^2*a'
Delta_2' = a'd + ad' - 2bb'
Delta_2' = a'P + aP'
P' = (Delta_2' a - Delta_2 a')/a^2.
```

At contact `P=0`,

```text
Delta_2' = aP'.
```

Under H1 (`a>0`), determinant and pivot derivative orientations agree.

This is theorem-backed **generic contact calculus**. It does not prove a contact exists, a production arithmetic sign, global Schur monotonicity, first-bad exclusion, negative-root exclusion or RH.

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
- **#178:** complete fixed-Q derivative implementation validated; raw nonzero-width derivative boxes unresolved.
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

The active strategy is now explicitly a **same-state incompatibility** search rather than a requirement for one RH-sized miracle lemma.

### Finite lane

```text
1. centered H1 recovery from point a(L0)>0 + rigorous a'(I)
2. inside recovered H1, retry the theorem-backed Schur derivative graph
3. if still unresolved, add Delta_2'' and centered mean-value/Taylor propagation
4. only after signed left/right neighborhoods, attempt interval Newton/Krawczyk
```

### Formal Pair-A lane

The production fixed-cell theorem inventory already contains exact decompositions of the form

```text
M_Q(L) = -log(L) I + R_Q(L).
```

The next formal target is a normalization-safe production/Hermitian Schur-envelope theorem that isolates the universal drift

```text
P'_log = -||u_L||^2/L
```

plus an exact scalar production remainder derivative. The hoped-for second lemma is a source-specific contact-local remainder bound forcing an orientation incompatible with first-bad crossing.

## Production bridge firewalls

- the q13 research integer shell generator spans the same one-dimensional shell as Lean's canonical cubic shell but is not theorem-identified at the same magnitude;
- formal production is complex Hermitian while #182 is generic real 2x2 calculus;
- existing source-coordinate `omega` derivative transport is not aperture-`L` derivative control;
- do not silently discard moving-optimizer derivative terms;
- global minimizing-Schur monotonicity remains quarantined;
- q13 whole-cell positivity alone would still be a finite result until generalized to the arbitrary retained first-bad state.

## Documentation authority

Current living state is maintained in:

- `research/RHRC/CURRENT_RESEARCH_PLAN.md`;
- `research/RHRC/RESEARCH_LEADS.md`;
- `research/RHRC/RESEARCH_LEADS_POST_182_SCHUR_ENVELOPE_CONTACT_ORIENTATION_DELTA.md`;
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
- generic #182 contact calculus is not a canonical arithmetic sign law.
- determinant and pivot minima are distinct optimization targets.
- simultaneous parity badness and odd-selected coverage remain open.
- negative-root exclusion is not the terminal Mathlib `RiemannHypothesis` statement without the final seam.

**RH remains OPEN.**
