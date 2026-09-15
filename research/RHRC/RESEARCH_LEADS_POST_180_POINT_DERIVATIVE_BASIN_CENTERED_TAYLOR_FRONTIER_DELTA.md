# RHRC research-leads delta after PR #180

> **Claim firewall: RH remains OPEN.**

## Authority

```text
THEOREM AUTHORITY
PR #163
validated theorem head = b418ff034428f92594bab0e5b8276181a086ee4b
validated theorem tree = c397b3a015ea54e38ecfe626d6e29556fe963839

LATEST RESEARCH EVIDENCE
PR #180
validated research head = a87469da9e611b53ae400cb4b18ce4afeb94e6d2
merge = 93ea3df51f2671e316197c1530ea504dee76e821
research tree = 8199cdc543f1b761c70466dfd602c143a277e6a2
RHRC #1077 = SUCCESS
Lean #837 = SUCCESS
Permansson #850 = SUCCESS

CONTROL SEMANTIC AUTHORITY
PR #117
selected first break = E4A4-SCHUR-FB-05
```

#180 contains no Lean theorem change.

## What became rigorously true in the research layer

**EXPERIMENTAL SIGNAL — rigorous finite:** the frozen six-primary Q14 exact-center derivative basin is minimum-oriented.

```text
point disposition = POINT_DERIVATIVE_BASIN_BRACKETED
orientation = MINIMUM_ORIENTED
left_negative_labels = all three frozen left centers
right_positive_labels = all three frozen right centers
usable_primary_count = 6
```

The exact-center Schur graph has the same minimum-oriented six-center sign pattern where its H1 prerequisite is certified.

**DERIVED, conditional only on the already-available continuity framework:** at least one zero of `Delta_2'` lies between a certified left-negative and right-positive point. This is stationary existence only. It is not uniqueness, a local-minimum theorem, or a sign theorem for `Delta_2` at the stationary point.

## What #180 did not establish

The proposed nonzero-width Schur comparison did not reach the width-comparison stage on the six primary boxes. The certifier reports

```text
representation disposition = SCHUR_OUT_OF_H1_SCOPE
applicable_primary_count = 0
sign_recovery_labels = []
strict_width_gain_labels = []
material_2x_gain_labels = []
uniqueness_claim = false
```

Therefore it is incorrect to summarize #180 as “Schur materially narrowed the six primary derivative boxes.” The correct state is stronger in one direction and weaker in another: the point derivative orientation is fully visible, but finite-width H1 certification is the first gate blocking the Schur interval representation.

The value event remains

```text
NO_BAD_OR_H1_LOSS_INTERVAL_CERTIFIED
```

which is not a proof of H1 over the boxes and not a positivity theorem.

## What changed mathematically

Before #180, the first question was whether the true derivative orientation was visible at all near the frozen basin. The answer is now yes at the exact frozen points. The interval failure is therefore a propagation/correlation problem, not evidence that the derivative itself is numerically zero.

The Schur experiment sharpens the obstruction further: on nonzero-width boxes the immediate problem is not yet Schur derivative width; it is certification of the H1 prerequisite `a(L)>0`.

## Selected finite continuation

The highest-information order is now:

```text
1. centered H1 recovery
     a(L0) > 0 at the existing frozen center
     + rigorous first-derivative enclosure a'(I)
     -> a(L0) + (I-L0)*a'(I)

2. if H1 is recovered, rerun the Schur derivative representation
     Delta_2 = aP
     Delta_2' = a'P + aP'

3. only if derivative sign remains unresolved, build Delta_2''
     Delta_2'' = a''d + 2a'd' + ad'' - 2(b')^2 - 2bb''
     and centered propagation
     Delta_2'(L)=Delta_2'(L0)+(L-L0)Delta_2''(xi)

4. only after signed finite neighborhoods, isolate the stationary point
     with interval Newton/Krawczyk or another rigorous root isolator

5. only after isolation, certify the sign of Delta_2 at the stationary state.
```

Start with the tightest inherited left/right pair. Do not move the centers toward a numerically prettier minimum.

## Structural theorem clue exposed by the accumulated inventory

**PROVED prior infrastructure:** fixed-cell source and intrinsic-predecessor modules preserve an exact `-log L` scalar coefficient through the production projections, with analytic remainder infrastructure.

**LEAD / HYPOTHESIS:** theoremize the actual Schur-envelope derivative and exploit

```text
A(L) = -log(L) I + R(L)
P'(L) = Re <u_L,A'(L)u_L>
      = -||u_L||^2/L + Re <u_L,R'(L)u_L>.
```

No project theorem currently supplies the displayed production-interface envelope derivative or the required sign bound on the remainder drift. Source-coordinate derivative transport is not automatically aperture-`L` derivative control.

At H1 contact, the algebra

```text
Delta_2 = aP
P=0 => Delta_2'=aP'
```

shows why a contact-local derivative law could be enough. This is deliberately weaker than global Schur monotonicity and does not revive DR-022.

## Falsification checks

- If centered `a` propagation cannot prove `a>0` even on the tightest inherited boxes, the immediate H1-recovery idea fails and the representation for `a` must change.
- If centered H1 succeeds but the Schur derivative remains sign-unresolved, then build/benchmark `Delta_2''`; do not merely add precision/subdivision to the same graph.
- If the `-1/L` drift and arithmetic remainder nearly cancel or reverse orientation at the frozen centers, kill or narrow the log-drift domination hypothesis before theorem engineering around it.
- Do not drop the derivative of the moving minimizing state unless a genuine envelope theorem proves the cancellation.
- Do not treat point-bracket stationary existence as stationary uniqueness.
- Do not infer `Delta_2(L*)>0` from derivative orientation alone.

## Highest-leverage next moves

1. **Centered H1 preflight** using existing `a`/`a'` evaluators; no second derivative required.
2. **Schur derivative retry only inside centered-certified H1 scope.**
3. **Second-order centered derivative propagation** if step 2 remains unresolved.
4. **Cheap drift-decomposition diagnostic** at the same frozen centers to test whether the proved `-log L` structure plausibly explains the observed orientation.
5. **Only then** stationary isolation and local minimum sign.

## Claim firewall

```text
PROVED theorem authority: through #163
EXPERIMENTAL SIGNAL: #180 exact-center minimum-oriented Q14 derivative basin
DERIVED: stationary existence between opposite-signed points if continuity is invoked
LEAD: centered H1 recovery / log-drift remainder domination / contact sign transfer
OPEN: finite-width derivative sign neighborhoods
OPEN: stationary uniqueness
OPEN: sign of Delta_2 at the stationary state
OPEN: q13 whole-cell barrier classification
OPEN: FB-05
OPEN: negative-root exclusion
OPEN: RH
```

**RH remains OPEN.**