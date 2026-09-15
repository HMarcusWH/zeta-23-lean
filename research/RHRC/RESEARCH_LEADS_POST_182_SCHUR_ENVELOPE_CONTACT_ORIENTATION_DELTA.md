# Post-#182 research delta — theorem-backed Schur contact orientation and production remainder frontier

> **Claim firewall: RH remains OPEN.**

## Exact validated object

```text
PR #182
validated theorem head = 0c3f63cdc4774ba1a68b21d1558ea0ee860a938d
merged theorem commit = a69160d37a84049711aaff6c3d5db804583a7306
validated theorem tree = e0b260b3b3a1ed470d54c14d8c0c46b32379f3fb
RHRC #1082 = SUCCESS
Permansson #855 = SUCCESS
```

The exact module added by #182 is `Zeta23/CCM/SchurEnvelopeDerivative.lean`, imported by `Zeta23/CCM.lean` and therefore inside the authoritative aggregate CCM build. No claim registry, promoted binding, boundary, or terminal RH surface was changed.

## What became formally true

For a generic real symmetric 2x2 block

```text
H = [[a,b],[b,d]]
P = d - b^2/a
Delta_2 = a*d - b^2
```

PR #182 proves, under the stated nonzero/derivative hypotheses:

```text
Delta_2 = a P
P' = d' - 2*(b/a)*b' + (b/a)^2*a'
Delta_2' = a'd + ad' - 2bb'
Delta_2' = a'P + aP'
P' = (Delta_2' a - Delta_2 a')/a^2
```

It also proves actual `HasDerivAt` theorems for `P` and `Delta_2`.

At Schur contact `P=0`:

```text
Delta_2' = a P'.
```

Under H1 (`a>0`), Lean proves both positive and negative orientation equivalences between determinant and pivot derivatives.

**PROVED:** the generic 2x2 contact-orientation transfer.

**NOT PROVED:** contact existence, contact uniqueness, a zeta-arithmetic sign for `P'`, finite-width H1, global Schur monotonicity, first-bad exclusion, negative-root exclusion, or RH.

## What changed

Before #182, the raw determinant derivative, quotient-rule pivot derivative and correlation-preserving envelope derivative were exact executable research identities checked in the post-#179/#180 R003 stack. After #182, the generic real 2x2 algebra/calculus connecting those representations is theorem authority.

This removes one proof-engineering layer from FB-05. Future work does not need to re-prove the generic quotient/product calculus every time the q13 microscope is used.

The remaining Pair-A burden is now source-specific:

```text
generic contact calculus                PROVED / #182
production-interface attachment         OPEN
-log(L) identity drift in envelope       OPEN at the required Schur interface
source-specific remainder derivative    OPEN
opposing contact-orientation inequality OPEN
```

## Upstream implications

The existing fixed-cell production inventory already proves exact identities of the form

```text
M_Q(L) = -log(L) I + R_Q(L)
```

through parity compression and intrinsic predecessor compression. It also proves scalar-coordinate analyticity of the lifted frozen remainder.

Therefore the next formal work should consume those interfaces rather than rebuild aperture dependence from the raw source formula.

A normalization warning is now explicit. The q13 research tooling uses an exact integer predecessor/shell basis `[W|c]`; its shell generator spans the same one-dimensional shell as Lean's canonical cubic shell but is not currently theorem-identified with the same magnitude. The finite code records `||W||^2` and `||c||^2` explicitly.

Accordingly, the next production theorem should prefer an invariant/Hermitian formulation rather than silently identifying the research integer generator with Lean's canonical shell normalization.

## Downstream implications

The universal logarithmic drift in raw orthogonal coordinates should contribute

```text
a'_log = -||W||^2 / L
b'_log = 0
d'_log = -||c||^2 / L.
```

For `x=b/a` and `u=c-xW`, this gives the invariant candidate

```text
P'_log = -(||c||^2 + x^2 ||W||^2)/L
       = -||u||^2/L,
```

using `W ⟂ c`.

The structural Pair-A target therefore becomes

```text
P'(L) = -||u_L||^2/L + remainder_drift(L,u_L)
```

followed by a source-specific contact-local bound on `remainder_drift` strong enough to force an orientation incompatible with first-bad contact geometry.

This is **LEAD / HYPOTHESIS** until the exact production interface and bound are theoremized.

## Resurrected routes

DR-022 global minimizing-Schur monotonicity remains quarantined. #182 does not show `P'` has one sign globally.

What is resurrected is only the local envelope/contact mechanism: at a contact, any independently proved production sign law for `P'` transfers immediately to `Delta_2'` under H1.

The #180 exact-center research basin also becomes more useful because its Schur representation now sits on theorem-backed generic calculus rather than only executable algebra. Its finite-width obstruction is unchanged: the primary nonzero-width boxes are still `SCHUR_OUT_OF_H1_SCOPE`.

## New RH-relevant clue — LEAD

The incompatibility program no longer needs a theorem about global positivity or monotonicity. A much weaker pair could suffice:

```text
A. first-bad/contact geometry forces one local crossing orientation;
B. canonical -log(L) drift plus controlled remainder forces the opposite orientation.
```

Both statements must apply to the same state, aperture, parity, normalization and production object.

## Falsification checks

1. **Remainder domination test.** Numerically/interval-certify the logarithmic piece and arithmetic remainder piece separately at the frozen #180 centers. If the remainder routinely overwhelms or reverses the universal drift, Pair A should be downgraded quickly.
2. **Normalization test.** Do not replace the research integer shell with Lean's canonical shell without a theorem identifying their scale, or use an invariant statement where the scale cancels.
3. **Complex/Hermitian test.** The formal production carrier is complex Hermitian. The generic #182 theorem is real 2x2 calculus. A production bridge must either prove a real specialization or theoremize the Hermitian `|b|^2/a` form before specializing.
4. **Moving-state test.** Do not silently discard derivatives of a moving optimizer. The Schur-envelope cancellation must be formal at the exact interface used.
5. **Source-coordinate test.** Existing source-coordinate `omega` derivative transport is not aperture-`L` derivative control.
6. **Global-monotonicity test.** A local contact theorem is allowed; a global fixed-sign `P'` theorem remains DR-022 unless new hypotheses exclude the known sign-changing behavior.
7. **Mustache test.** The opposing arithmetic lemma must not simply restate successor positivity, negative-root exclusion, full Weil positivity, or another RH-equivalent target.

## Highest-leverage next moves

### Finite research lane

```text
1. centered H1 recovery on the exact frozen #180 boxes
2. theorem-backed Schur-box retry only inside centered-certified H1
3. Delta_2'' / centered derivative propagation only if sign remains unresolved
4. interval Newton/Krawczyk only after signed left/right neighborhoods
```

### Formal Pair-A lane

```text
1. choose an invariant/Hermitian production Schur-envelope interface
2. attach it to the already-proved fixed-cell -log(L)I + remainder decomposition
3. isolate the exact -||u||^2/L universal drift
4. expose the remainder as an exact scalar-coordinate derivative
5. falsify or prove a source-specific contact-local remainder bound
6. compose with #182 contact orientation
```

## Standing questions

> Given everything now formally true through #182, can the production arithmetic force a contact orientation that first-bad geometry forbids?

> Can the universal `-log(L)` drift be isolated at the exact retained state without a normalization mismatch or hidden moving-state term?

> What is the cheapest rigorous experiment that tells us whether the arithmetic remainder can dominate the universal drift in the dangerous q13/Q14 regime?

**RH remains OPEN.**
