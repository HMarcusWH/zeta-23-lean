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
merged research PR = #186
validated research head = 7d277a99437d98fdb7c831f25a130eac07f1b3af
merged research commit = 0494658a87d29eeb2124aa16232c264c21d23c18
RHRC #1091 = SUCCESS
Permansson #864 = SUCCESS
research disposition = DOMINATION_SIGNAL_MIXED

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
same-state shifted Riesz x cross-parity source composition              PROVED / #161
mixed quadratic-normal seventh source jet -> M4                         PROVED / #163
finite-prime sampling of the same mixed source observable               PROVED / #163
mixed-jet squared Riesz-8/Riesz-9 boundary coupling                     PROVED / #163
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
any valid narrowed source-specific contact-orientation law              OPEN
first-bad contact existence/orientation composition                     OPEN
q13 finite-width H1 / whole-cell sign-contact classification            OPEN / ACTIVE
simultaneous even/odd bad exclusion                                     OPEN
odd-selected first-bad branch closure                                   OPEN
negative-root exclusion                                                 OPEN
outside-strip/trivial-zero seam + Mathlib RH wrapper                    OPEN
RH                                                                      OPEN
```

## What #184 proved

PR #184 moves the contact-orientation route into actual complex-Hermitian production geometry. Lean theoremizes

```text
P = d - |b|^2/a
M~(t) = -t I + R~(t)
P_t' = -envelopeNormSq + remainderEnvelopeDerivative
```

with the exact fixed-cell bridge to `parityCompressedCanonical`, N2 predecessor/canonical-cubic-shell reconstruction and orthogonality, and the conditional implication

```text
remainderEnvelopeDerivative < envelopeNormSq -> P_t' < 0.
```

#184 does **not** prove that the production arithmetic remainder satisfies the domination premise, contact existence/uniqueness, an opposing first-bad orientation, negative-root exclusion or RH.

## What #186 discovered

PR #186 deliberately tried to falsify the post-#184 domination clue before further Lean investment. It reused the exact frozen #180 q13/Q14 N2/K3/even schedule and evaluated the physical-aperture form

```text
dP/dL = -E/L + dR/dL
margin = E/L - dR/dL
rho = L*dR/dL/E.
```

The green certificate returned

```text
DOMINATION_SIGNAL_MIXED
```

with:

```text
positive margin:
  det_left_o2^-10_r2^-13
  det_left_o2^-13_r2^-16

negative margin:
  det_right_o2^-10_r2^-13
  det_right_o2^-13_r2^-16
  det_left_o2^-16_r2^-19
  det_right_o2^-16_r2^-19

unresolved primary exact centers: none
finite-width scope: FINITE_WIDTH_OUT_OF_H1_SCOPE
```

So the broad claim that the production remainder is uniformly dominated by the universal negative log drift is **experimentally falsified on this frozen finite panel**. That does not invalidate #184: its theorem is conditional. It also does not establish a general opposite-sign theorem.

## Current active path — FB-05

The active strategy remains a **same-state incompatibility** search. #186 changes the immediate target.

### Research lane — explain the mixed split

Keep the #186 schedule frozen. Do not move centers or refit the basin. Search for a canonical/theorem-connectable variable explaining why two states satisfy the domination inequality and four do not.

Candidate diagnostics include:

```text
E
dR/dL
rho
P_L'
a, |b|, d
normalized predecessor/shell coupling
fixed-Q cell position
position relative to the #180 minimum-oriented basin
opposite-parity / ancestry controls
```

A useful condition must not merely encode the target margin, depend on arbitrary normalization, fail controls, or require finite-width H1 where H1 is not certified.

### Formal lane — sign-neutral derivative witnesses

The analytic infrastructure already proves entrywise holomorphy of the complete frozen complex source remainder. A useful next theorem package can transport this through exact parity projection and N2 predecessor/canonical-shell pairings to actual real derivative witnesses for

```text
a_R, Re b_R, Im b_R, d_R
```

and instantiate #184's algebraic identity as an actual production `HasDerivAt` Schur theorem.

After #186 this is infrastructure, not evidence for a universal domination law.

### Composition lane

A surviving Pair-A route now has the form

```text
canonical selector C on the exact retained/contact state
  -> narrowed contact-local remainder domination
  -> #184 gives negative pivot orientation
  -> independent first-bad theorem gives incompatible property
  -> same-state contradiction
```

If no theorem-connectable selector survives the frozen controls, Pair A should be downgraded and the project should prioritize the other FB-05 incompatibility pairs: negative-index/sampling rigidity, local-zero rigidity, and the two-parity squeeze.

## Production / coordinate firewalls

- the q13 research integer shell generator spans the same one-dimensional shell as Lean's canonical cubic shell but is not theorem-identified with the same magnitude;
- `t=log L` derivatives and physical-`L` derivatives differ by the factor `L` and must not be mixed;
- analyticity does not imply a useful domination bound;
- #186 mixed finite evidence is not a general sign theorem;
- finite-width Schur/remainder claims require certified H1;
- global minimizing-Schur monotonicity remains quarantined;
- q13/N2/K3 finite evidence does not automatically generalize to arbitrary retained first-bad states.

## Documentation authority

Current living state is maintained in:

- `research/RHRC/CURRENT_RESEARCH_PLAN.md`;
- `research/RHRC/RESEARCH_LEADS.md`;
- `research/RHRC/RESEARCH_LEADS_POST_186_REMAINDER_DRIFT_MIXED_DELTA.md`;
- `research/RHRC/OBSTRUCTION_LEDGER_POST_186_DELTA.md`;
- `research/RHRC/FB05_INCOMPATIBILITY_PROGRAM.md`;
- `research/RHRC/DOCUMENTATION_AUTHORITY.md`;
- `research/RHRC/VALIDATION_PROTOCOL.md`;
- `research/RHRC/routes/R003_ccm_bridge/README.md`;
- `research/RHRC/control_v2/CONTROL_STATE.json`.

Older dated deltas, external reviews and countermodel records remain historical evidence and are not rewritten to look current.

## Permanent firewalls

- RH remains OPEN.
- theorem authority is compiler evidence, not PR title or prose.
- research green is not theorem authority.
- a green falsification run may reject its tested hypothesis.
- finite Arb certification is not a global theorem.
- transformed negativity is not a contradiction.
- the contradiction must use incompatible properties of the exact same retained state/aperture/parity/normalization/production object.
