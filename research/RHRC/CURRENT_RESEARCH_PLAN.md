# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

Live GitHub head + exact compiler/CI evidence are authoritative dynamically. This file records the current theorem, research and control anchors and the active FB-05 execution order.

## Authority split

### Theorem authority

```text
latest theorem-bearing PR = #184
validated theorem head = a756494ebe7e2530715e996b9a9a341fbe07c683
merged theorem commit = 6f04e94473eb112b59eeaa2c6fc6ac6cbe7fe30e
validated theorem tree = 6c77cd470809959a403b3bcc5f08d39f4076fa4c
RHRC #1089 = SUCCESS
Permansson #862 = SUCCESS
```

### Latest research-evidence anchor

```text
latest merged research PR = #180
validated research head = a87469da9e611b53ae400cb4b18ce4afeb94e6d2
merged research commit = 93ea3df51f2671e316197c1530ea504dee76e821
research tree = 8199cdc543f1b761c70466dfd602c143a277e6a2
RHRC #1077 = SUCCESS
Lean #837 = SUCCESS
Permansson #850 = SUCCESS
```

### Control authority

```text
control-plane semantic anchor = PR #117
selected formal first break = E4A4-SCHUR-FB-05
terminal claim = RH_OPEN
```

The theorem, research and control anchors are intentionally separate. #184 advances theorem authority; #180 remains the latest research-only finite evidence; #117 remains the controller semantic authority.

## One-screen frontier

```text
PROVED THROUGH #184
  off-line zero
  -> retained regular cell-minimal first-bad certificate
  -> exact negative canonical source channel
  -> exact finite pole-prime discrepancy
  -> legal production Riesz engine and transformed negativity
  -> same-state shifted source/Riesz composition
  -> mixed quadratic-normal seventh jet
  -> exact finite-prime sampling of same observable
  -> exact R8-R9 squared-jet boundary
  -> generic real 2x2 Schur-envelope derivative                    #182
  -> generic complex-Hermitian 2x2 Schur calculus                  #184
  -> full frozen parity family on logarithmic cover                #184
  -> exact fixed-cell bridge to parityCompressedCanonical          #184
  -> N2 predecessor / cubic-shell reconstruction + orthogonality   #184
  -> algebraic P_t' = -envelopeNormSq + remainderEnvelopeDerivative #184
  -> remainderEnvelopeDerivative < envelopeNormSq -> P_t' < 0      #184

RESEARCHED THROUGH #180
  q13/N2/K3/even reduced to exact 2x2 scalar barrier
  fixed-unit value representation selected
  complete fixed-Q physical-L derivative backend validated
  raw nonzero-width Delta_2' boxes unresolved
  exact-center six-point Q14 derivative basin minimum-oriented
  nonzero-width Schur boxes SCHUR_OUT_OF_H1_SCOPE

NOW — FB-05
  finite falsification lane:
    reuse exact #180 frozen Q14 schedule
    -> decompose physical-L Schur derivative into
         universal drift = -envelopeNormSq/L
         production remainder drift
    -> report domination margin envelopeNormSq/L - remainder_drift_L
    -> report coordinate-consistent ratio L*remainder_drift_L/envelopeNormSq
    -> only if this survives, invest in theoremizing the source-specific bound

  formal Pair-A lane:
    transport existing frozen-source holomorphy through
      parity projection + N2 predecessor/shell scalar pairings
    -> discharge actual real remainder-coordinate derivative witnesses
    -> instantiate the #184 algebraic identity as an actual production HasDerivAt theorem
    -> prove/falsify source-specific contact-local remainder domination
    -> compose with an independently theorem-backed incompatible first-bad contact orientation
```

## Exact #184 theorem package

PR #184 adds `Zeta23/CCM/HermitianSchurEnvelopeDerivative.lean` and `Zeta23/CCM/FrozenN2SchurLogDrift.lean` to the aggregate CCM build.

For a Hermitian 2x2 block with real diagonal coordinates `a,d` and complex off-diagonal coordinate `b`, Lean theoremizes the Schur pivot/determinant calculus with the correction `|b|^2/a`, including real-component `HasDerivAt` theorems for `Re b` and `Im b`. At contact and under H1, determinant and pivot derivative orientations agree.

The frozen production family is theoremized on logarithmic coordinate `t` as

```text
M~(t) = -t I + R~(t),
```

with an exact fixed-cell bridge back to the actual production `parityCompressedCanonical`. The N2/K3 geometry additionally proves exact predecessor-shell reconstruction, a nonzero canonical cubic shell, and predecessor-shell orthogonality.

For derivative data having the required coordinate form, #184 proves the algebraic decomposition

```text
P_t' = - envelopeNormSq + remainderEnvelopeDerivative
```

and therefore

```text
remainderEnvelopeDerivative < envelopeNormSq -> P_t' < 0.
```

### Exact #184 firewall

#184 does **not** yet assemble the actual source-specific real scalar derivative witnesses from the already-proved complex remainder holomorphy. Therefore it does not yet provide a fully instantiated production `HasDerivAt` theorem for the N2 Schur pivot, and it does not prove the source-specific domination inequality.

It also does not prove contact existence/uniqueness, a first-bad crossing orientation theorem, global Schur monotonicity, first-bad exclusion, negative-root exclusion, or RH.

## Research state through #180

The post-#163 research sequence remains consumed evidence/infrastructure:

```text
#165 endpoint scalar audit
#166 true shifted-state finite discriminator
#167 Q16 whole-cell interval method falsification
#168 threshold moment jets / Q17 microscope
#170 theorem-aligned [W|c] Schur visibility/background audit
#172 threshold-to-threshold production barrier audit
#174 exact q13/N2/K3/even 2x2 scalar barrier
#176 fixed-unit value representation accepted
#178 complete fixed-Q physical-L derivative implementation; raw derivative boxes unresolved
#180 exact-center derivative orientation; nonzero-width Schur graph out of H1 scope
```

The exact #180 finite result is:

```text
POINT_DERIVATIVE_BASIN_BRACKETED
MINIMUM_ORIENTED
left centers:  3/3 Delta_2' < 0
right centers: 3/3 Delta_2' > 0
SCHUR_OUT_OF_H1_SCOPE on all primary nonzero-width Schur boxes
applicable_primary_count = 0
uniqueness_claim = false
```

No bad interval or H1-loss interval is certified.

## Active lead A — falsify the post-#184 domination clue first

The theorem and research coordinates must not be mixed.

#184 uses `t = log L`, so

```text
dP/dt = -E + dR/dt.
```

The #178/#180 backend differentiates with respect to physical aperture `L`, hence the equivalent research identity is

```text
dP/dL = -E/L + dR/dL.
```

The coordinate-consistent domination test is therefore

```text
dR/dL < E/L
```

or equivalently

```text
L * dR/dL < E.
```

The next research PR should reuse the exact frozen #180 schedule and report, at the same q13/Q14 N2/K3 states:

```text
universal_log_drift_L = -E/L
production_remainder_drift_L
full_pivot_derivative_L
domination_margin_L = E/L - production_remainder_drift_L
normalized_ratio = L * production_remainder_drift_L / E
```

It must cross-check that

```text
full_pivot_derivative_L
  = universal_log_drift_L + production_remainder_drift_L.
```

This is a falsification experiment, not theorem authority. If the margin is not robustly positive on the dangerous states, the proposed domination formulation should be revised before further Lean investment.

## Active lead B — actual production derivative witnesses

The repo already proves entrywise holomorphy of the complete frozen complex source remainder on the punctured safe strip. The next formal bridge is therefore finite-dimensional transport rather than new pole/arch/prime analyticity:

```text
complex frozen source remainder holomorphy
  -> parity-compressed remainder scalar analyticity
  -> N2 predecessor/shell pairings
  -> real derivatives for a_R, Re b_R, Im b_R, d_R
  -> actual production HasDerivAt Schur identity
```

For N=2 the intrinsic predecessor has complex dimension one and the successor shell has dimension one, so the production microscope really is a 1D->2D Hermitian problem. The canonical cubic shell already supplies the distinguished shell direction; no research integer-shell magnitude may be silently substituted for it.

## What remains formally open

```text
explicitCanonicalSourceMoment != 0 -> M4 != 0
M4 != 0 -> explicitCanonicalSourceMoment != 0
finite production samples determine h^(7)(0)
canonicalPolePrimeRieszEndpointScalar L 8 >= 0
canonicalPolePrimeRieszEndpointScalar L 8 != 0
actual N2 production remainder scalar derivative witnesses
actual production HasDerivAt Schur log-drift identity
source-specific production remainder domination/contact-orientation bound
first-bad contact existence/orientation composition on the same retained state
centered finite-width H1 on the #180 boxes
q13/N2/K3/even whole-cell sign/contact/nonvanishing
simultaneous even/odd bad exclusion
odd-selected first-bad closure
independent contradiction-producing canonical arithmetic restriction
negative-root exclusion
outside-strip/trivial-zero terminal seam
RiemannHypothesis
```

## Reusable firewalls

- #184 closes the Hermitian/log-cover algebraic interface, not the source-specific remainder derivative bound;
- analyticity does not imply a useful derivative magnitude bound;
- `t=log L` derivative statements must be converted before comparison with physical-`L` R003 derivatives;
- determinant and pivot minima are distinct because `P=Delta_2/a` and `a(L)` varies;
- fixed-unit value conditioning does not automatically give derivative sign discrimination;
- point orientation is recoverable, but the current nonzero-width Schur graph first fails at H1 scope;
- global aperture / global minimizing-Schur monotonicity remains quarantined;
- q13/N2/K3 evidence does not automatically generalize to every retained first-bad state;
- research green is not theorem promotion;
- RH remains OPEN.

## Highest-leverage next move

Run the coordinate-consistent post-#184 remainder/envelope decomposition on the exact frozen #180 Q14 states before theoremizing the actual source-specific derivative witnesses.

Standing question:

> Given everything theoremized through #184 and rigorously researched through #180, does the canonical arithmetic remainder fail to outrun the universal negative log-envelope drift at the same dangerous state?

If that survives falsification:

```text
actual production derivative witnesses
  -> source-specific domination theorem
  -> same-state contact-orientation incompatibility
  -> FB-06 same-state contradiction / negative-root exclusion
  -> FB-07 outside-strip/trivial-zero seam + Mathlib RH wrapper
```

Detailed newest synthesis:
`RESEARCH_LEADS_POST_184_HERMITIAN_LOG_DRIFT_REMAINDER_DOMINATION_DELTA.md`.

**RH remains OPEN.**