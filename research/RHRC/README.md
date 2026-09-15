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
merged research PR = #186
validated research head = 7d277a99437d98fdb7c831f25a130eac07f1b3af
merged research commit = 0494658a87d29eeb2124aa16232c264c21d23c18
RHRC #1091 = SUCCESS
Permansson #864 = SUCCESS
research disposition = DOMINATION_SIGNAL_MIXED

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
any valid narrowed production contact-orientation bound               OPEN
same-state first-bad contact orientation composition                  OPEN
q13 finite-width H1 / whole-cell sign-contact classification          OPEN / ACTIVE
simultaneous even/odd bad exclusion                                   OPEN
odd-selected branch closure                                           OPEN
negative-root exclusion                                               OPEN
terminal zeta/Mathlib seam                                            OPEN
RH                                                                    OPEN
```

## What #184 established

The production/Hermitian interface is theorem-backed. In the exact stated scopes Lean proves

```text
P = d - |b|^2/a
M~(t) = -t I + R~(t)
P_t' = -envelopeNormSq + remainderEnvelopeDerivative
```

along with the fixed-cell bridge to `parityCompressedCanonical`, N2 predecessor/canonical-cubic-shell reconstruction and orthogonality, and the conditional implication

```text
remainderEnvelopeDerivative < envelopeNormSq -> P_t' < 0.
```

#184 does not prove the arithmetic premise of that implication, contact existence/uniqueness, an opposing first-bad orientation, negative-root exclusion or RH.

## What #186 changed

#186 reused the exact frozen #180 q13/Q14 N2/K3/even schedule and evaluated the corresponding physical-aperture decomposition

```text
dP/dL = -E/L + dR/dL
margin = E/L - dR/dL
rho = L*dR/dL/E.
```

The green research certificate returns

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

unresolved primary exact centers: none
finite-width scope: FINITE_WIDTH_OUT_OF_H1_SCOPE
```

Therefore the simple universal production-remainder domination hypothesis is falsified in this finite scope. This is a successful falsification result, not a CI failure and not a contradiction of #184's conditional theorem.

## Immediate frontier — FB-05

### Research lane: explain the mixed split

Do **not** move/refit the frozen #186 schedule. Compare the two positive-margin states with the four negative-margin states using canonical/theorem-connectable quantities such as

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

The goal is not to fit six points. The goal is a condition `C(state)` that is independently meaningful and could plausibly be forced on the exact retained first-bad/contact state.

Reject a candidate if it restates the target margin, depends on arbitrary normalization, fails controls, or requires finite-width H1 outside certified scope.

### Formal lane: sign-neutral production derivative witnesses

The repo already proves entrywise holomorphy of the complete frozen complex source remainder. The next formal interface can still be:

```text
complex remainder holomorphy
  -> parity-compressed scalar analyticity
  -> N2 predecessor/canonical-shell pairings
  -> actual real derivative witnesses for a_R, Re b_R, Im b_R, d_R
  -> production HasDerivAt Schur identity
```

After #186 this is infrastructure, not evidence that universal domination is true.

### Composition lane

A surviving Pair-A contradiction would now require

```text
canonical selector C on the same state
  -> contact-local remainder domination
  -> #184 negative pivot orientation
  -> independently theorem-backed incompatible first-bad orientation
  -> same-state contradiction
```

If no theorem-connectable selector survives the finite controls, downgrade Pair A and prioritize the other incompatibility pairs in `FB05_INCOMPATIBILITY_PROGRAM.md`.

## Production normalization / coordinate firewall

The q13 research integer shell generator spans the same one-dimensional shell as Lean's canonical cubic shell but is not theorem-identified with the same magnitude. Formal theorem work should stay on the canonical intrinsic shell.

Also:

```text
d/dt with t=log L = L * d/dL.
```

Do not compare log-coordinate and physical-L derivative magnitudes without that factor. Analyticity proves derivative existence, not a useful domination estimate. A mixed finite sign pattern is not a general opposite-sign theorem.

Global Schur monotonicity remains quarantined.

## Current execution priority

1. run a predeclared mixed-split discriminator audit on the exact #186 frozen states;
2. test normalization, ancestry and parity controls before Lean investment;
3. theoremize the actual N2 remainder scalar derivative witnesses as a sign-neutral interface;
4. only if a canonical selector survives, formulate the narrowest contact-local sign theorem;
5. independently identify/prove the opposing first-bad property on the exact same retained state;
6. preserve `RH_OPEN` until negative-root exclusion and the terminal zeta/Mathlib seam are theorem-backed.

Newest research synthesis:
`RESEARCH_LEADS_POST_186_REMAINDER_DRIFT_MIXED_DELTA.md`.

Obstruction supplement:
`OBSTRUCTION_LEDGER_POST_186_DELTA.md`.

**RH remains OPEN.**
