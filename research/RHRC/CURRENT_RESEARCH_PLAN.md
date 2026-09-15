# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

Live GitHub head + exact compiler/CI evidence are authoritative dynamically. This file records the current theorem, research and control anchors and the active FB-05 execution order.

## Authority split

### Theorem authority

```text
latest theorem-bearing PR = #182
validated theorem head = 0c3f63cdc4774ba1a68b21d1558ea0ee860a938d
merged theorem commit = a69160d37a84049711aaff6c3d5db804583a7306
validated theorem tree = e0b260b3b3a1ed470d54c14d8c0c46b32379f3fb
RHRC #1082 = SUCCESS
Permansson #855 = SUCCESS
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

The theorem, research and control anchors are intentionally separate. #182 advances theorem authority; #180 remains the latest research-only finite evidence; #117 remains the controller semantic authority.

## One-screen frontier

```text
PROVED THROUGH #182
  off-line zero
  -> retained regular cell-minimal first-bad certificate
  -> exact negative canonical source channel
  -> exact finite pole-prime discrepancy
  -> legal production Riesz engine and transformed negativity
  -> same-state shifted source/Riesz composition
  -> mixed quadratic-normal seventh jet
  -> exact finite-prime sampling of same observable
  -> exact R8-R9 squared-jet boundary
  -> generic real 2x2 Schur-envelope derivative
  -> at H1 contact, determinant and pivot derivative orientations agree

RESEARCHED THROUGH #180
  q13/N2/K3/even reduced to exact 2x2 scalar barrier
  fixed-unit value representation selected
  complete fixed-Q derivative backend validated
  raw nonzero-width Delta_2' boxes unresolved
  exact-center six-point Q14 derivative basin minimum-oriented
  nonzero-width Schur boxes SCHUR_OUT_OF_H1_SCOPE

NOW — FB-05
  finite lane:
    centered H1 recovery
    -> theorem-backed Schur-box retry
    -> Delta_2'' centered propagation only if needed
    -> interval Newton/Krawczyk only after signed neighborhoods

  formal Pair-A lane:
    invariant/Hermitian production Schur-envelope bridge
    -> attach fixed-cell -log(L)I + remainder
    -> isolate -||u||^2/L universal drift
    -> exact production remainder derivative
    -> source-specific contact-local opposing orientation
```

## Exact #182 theorem package

`Zeta23/CCM/SchurEnvelopeDerivative.lean` is imported into the aggregate CCM build and proves for the generic real 2x2 block

```text
H = [[a,b],[b,d]]
P = d - b^2/a
Delta_2 = a*d - b^2
```

that, under the stated nonzero/derivative hypotheses,

```text
Delta_2 = a P
P' = d' - 2*(b/a)*b' + (b/a)^2*a'
Delta_2' = a'd + ad' - 2bb'
Delta_2' = a'P + aP'
P' = (Delta_2' a - Delta_2 a')/a^2.
```

At contact `P=0`:

```text
Delta_2' = a P'.
```

Under H1 (`a>0`), positive and negative determinant derivative orientation is equivalent to positive and negative pivot derivative orientation.

This is **PROVED generic calculus**. It is not yet a production arithmetic sign theorem.

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
#178 complete fixed-unit derivative implementation; raw derivative boxes unresolved
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

## Active lead A — finite-width propagation

The finite laboratory is

```text
H(L) = [[a(L),b(L)],[b(L),d(L)]]
Delta_2(L)=a(L)d(L)-b(L)^2
H1 <-> a(L)>0
P(L)=Delta_2(L)/a(L) in H1.
```

Run in this order:

```text
1. centered H1 recovery on the frozen #180 boxes
     certify point a(L0)>0
     use the already-validated rigorous a'(I)
     enclose a(I) by a(L0)+(I-L0)*a'(I)

2. if H1 is recovered
     retry the Schur-factorized derivative on the same boxes
     use #182 as theorem authority for the generic identity

3. only if sign remains unresolved
     implement/bound Delta_2''
     use centered mean-value/Taylor propagation from the already-signed centers

4. only after signed left/right neighborhoods
     use interval Newton/Krawczyk for stationary isolation

5. only after a stationary state is isolated
     certify the sign of Delta_2 at that state/basin.
```

Do not repeat the same raw assembled derivative boxes with only more precision/depth and call it a new route.

## Active lead B — production contact-orientation incompatibility

The project already proves fixed-cell production decompositions of the form

```text
M_Q(L) = -log(L) I + R_Q(L)
```

through parity compression and intrinsic predecessor compression, with analytic scalar-coordinate remainder infrastructure.

For orthogonal raw coordinates `W,c`, with `x=b/a` and `u=c-xW`, the universal scalar drift should contribute

```text
a'_log = -||W||^2/L
b'_log = 0
d'_log = -||c||^2/L
P'_log = -||u||^2/L.
```

The formal target is therefore an invariant/Hermitian production statement schematically of the form

```text
P'(L) = -||u_L||^2/L + remainder_drift(L,u_L).
```

Then seek/falsify a source-specific contact-local bound on `remainder_drift` strong enough to force an orientation incompatible with first-bad crossing.

### Production bridge firewalls

- #182 is real generic 2x2 calculus; production is complex Hermitian. Do not silently replace the Hermitian correction `|b|^2/a` by `b^2/a` without a real-specialization theorem.
- The research integer shell generator spans the same one-dimensional shell as Lean's canonical cubic shell but is not theorem-identified with the same magnitude. Prefer an invariant formulation or separately prove the scale bridge.
- Existing source-coordinate `omega` derivative transport is not aperture-`L` derivative control.
- Do not silently discard moving-optimizer terms; use an exact envelope theorem at the production interface.
- Global Schur monotonicity remains quarantined. The target is contact-local.

## What remains formally open

```text
explicitCanonicalSourceMoment != 0 -> M4 != 0
M4 != 0 -> explicitCanonicalSourceMoment != 0
finite production samples determine h^(7)(0)
canonicalPolePrimeRieszEndpointScalar L 8 >= 0
canonicalPolePrimeRieszEndpointScalar L 8 != 0
production/Hermitian Schur-envelope derivative bridge
production remainder contact-orientation bound
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

- scalarization does not eliminate interval dependency;
- determinant and pivot minima are distinct because `P=Delta_2/a` and `a(L)` varies;
- fixed-unit value conditioning does not automatically give derivative sign discrimination;
- point orientation is recoverable, but the current nonzero-width Schur graph first fails at H1 scope;
- generic #182 contact calculus does not provide a canonical arithmetic sign;
- global aperture / global minimizing-Schur monotonicity remains quarantined;
- q13 whole-cell positivity alone would still be finite evidence until generalized to the arbitrary retained first-bad state;
- research green is not theorem promotion;
- RH remains OPEN.

## Highest-leverage next move

Run the centered-H1 preflight on the frozen #180 Q14 side boxes while, in parallel, theoremizing the normalization-safe production Schur-envelope/log-drift interface.

Standing question:

> Given everything theoremized through #182 and rigorously researched through #180, can the same hypothetical first-bad contact be forced to have two incompatible local orientations?

Then:

```text
surviving independent arithmetic restriction
  -> compose with exact retained state
  -> FB-06 same-state contradiction / negative-root exclusion
  -> FB-07 outside-strip/trivial-zero seam + Mathlib RH wrapper
```

Detailed newest synthesis:
`RESEARCH_LEADS_POST_182_SCHUR_ENVELOPE_CONTACT_ORIENTATION_DELTA.md`.

**RH remains OPEN.**
