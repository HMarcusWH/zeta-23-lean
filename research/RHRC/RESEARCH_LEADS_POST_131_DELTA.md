# RHRC post-#131 research delta — exact source decomposition and A4b transition

> **Claim firewall: RH remains OPEN.**
>
> This is a dated post-green delta. It records what became newly visible after PR #131. It supersedes `RESEARCH_LEADS_POST_129_DELTA.md` for current priority, but does not rewrite that historical record.

## Exact authority

```text
PR #131 head = b0026683bcbf233afa947c7f15b57bcc4ddf31e3
PR #131 merge = 436d524d0cdeb5986d76dcbb988f771d19836c55
validated theorem tree = 5ad51fd877d51348f1af474b2864eb4ab3e0617a
RHRC #854 = SUCCESS
Permansson #627 = SUCCESS

RH = OPEN
```

The RHRC exact-head gate passed the claim/regression suite, Control-v2 smoke run, R003 source/normalization firewall, `lake build Zeta23.CCM`, `lake build Zeta23.ExceptionalZero`, and the forbidden-placeholder rejection gate.

## What became formally true

**PROVED / #131 — A4a source decomposition.**

For positive aperture, the production canonical source matrix is decomposed exactly into pole, corrected/reduced archimedean, and finite prime-power channels. In the quadratic-normal observable introduced in #129:

- the index-independent canonical archimedean scalar disappears exactly;
- the reduced archimedean term splits into diagonal and off-diagonal contributions;
- the finite prime channel becomes a von-Mangoldt weighted finite sum of the existing elementary `sourceMatrix` atoms;
- the pole matrix factors into even/odd profiles and the odd profile annihilates the even boundary-flat input, leaving one surviving even-profile channel.

The endpoint theorem is

```text
cubicDefectFunctional L K v
  = explicitCanonicalSourceMoment L K v
```

under `0 < L`, `2 <= K`, and `v` in the even Euclidean boundary-flat sector.

The explicit moment is exactly

```text
one surviving pole-even profile term
- reduced arch diagonal moment
- reduced arch off-diagonal moment
- finite von-Mangoldt weighted elementary sourceMatrix moments.
```

No sign, nonzeroness, branch exclusion, negative-root exclusion, or RH conclusion is proved.

## What changed mathematically

The #129 source moment is now visibly a **linear functional of the trial vector**. Matrix action is linear in `v`, pairing is against the fixed centered quadratic normal, and the normalizing denominator is independent of `v`.

Therefore a universal theorem of the form

```text
sourceMoment(v) > 0
```

for every legal even boundary-flat `v` is not a viable A4b target: replacing `v` by `-v` reverses the moment. Over the complex carrier, phase covariance makes the same obstruction stronger.

This does **not** rule out a sign, real-part, phase, or nonvanishing statement for the canonically oriented secular trial vector after composing with other theorem-backed branch data. It rules out raw universal-sector positivity as the mechanism.

## New route classification

### PROVED

- exact source-channel decomposition;
- exact cancellation of the index-independent archimedean scalar in the active observable;
- exact reduced arch diagonal/off-diagonal split;
- exact finite von-Mangoldt prime atomization;
- exact pole rank-two profile factorization and odd-profile cancellation on the even boundary-flat sector;
- `cubicDefectFunctional = explicitCanonicalSourceMoment` under the #129 hypotheses.

### DERIVED

- the explicit source moment is linear in the trial vector;
- raw universal positivity/nonnegativity on the whole vector space cannot hold except in a degenerate zero-functional sense;
- because `sourceMatrix 0 = 0` and `sourceMatrix 1 = 2 I`, while the quadratic-normal observable annihilates scalar identity matrices, the elementary source observable vanishes at both dictionary endpoints `omega=0` and `omega=1`.

These are consequences of proved identities but are not yet separately promoted as named Lean theorems.

### LEAD / HYPOTHESIS

1. **A4b compositional source invariant.** Study the actual quantity entering cross-parity transfer,

   ```text
   Gamma * explicitCanonicalSourceMoment(u_+)
   ```

   or the exact overlap-times-source form at an even root, rather than the source moment in isolation.

2. **Elementary source-atom shape.** Treat

   ```text
   omega -> quadraticNormalMatrixMoment K (sourceMatrix omega K) v
   ```

   as the smallest source-sensitive object. Endpoint vanishing suggests looking for exact factorization, symmetry, monotonicity, convexity, controlled real part, or an interior extremal principle. None is currently proved.

3. **Potential-level arch/prime composition.** Prime atoms are divided-difference matrices, and the reduced arch off-diagonal channel has the same divided-difference shape. Test whether a smaller potential-level identity unifies them. Matching diagonal data is a theorem obligation, not an assumption.

4. **Regular branch A4b.** Combine `k=0`, `Re sigma0<0`, predecessor nonnegativity, exact cross-parity transfer, and the explicit source decomposition. Seek either contradiction or a sharply smaller canonical regular class.

5. **Resonant branch A4c.** Combine `k!=0`, `(-lam)K(R_lam b)=k`, predecessor nonnegativity, exact cross-parity transfer, and the same source decomposition.

## Falsification checks

Before theoremizing any source inequality:

- test `v -> -v` and complex phase rotation;
- test source moment zero, overlap zero, `Gamma=0`, and `alpha=0`;
- do not divide by overlap, `Gamma`, `alpha`, or source moment without an independent nonzeroness theorem;
- test the elementary source observable near `omega=0` and `omega=1`;
- verify that any proposed arch/prime unification includes the correct diagonal data, not only the off-diagonal divided difference;
- rerun generic structural fixtures to confirm that the new argument genuinely spends canonical source values;
- retain the predecessor correction in `D c+` and never use D as unitary/isometric;
- remember that root uniqueness is not root absence.

## Highest-leverage next theorem tranche

### A4b-0 — source-expanded cross-parity root transfer

The next theorem-bearing PR should make the #131 decomposition directly available at the #129 secular root interface. A useful tranche would:

1. theoremize linearity/negation/scalar covariance of `explicitCanonicalSourceMoment` so the sign firewall is permanent;
2. compose `evenQuadraticSourceMoment_eq_explicitCanonicalSourceMoment` into `cubicSecularScalar_crossParity_source_transfer` and `cubicSecularScalar_odd_eq_overlap_mul_source_of_even_root`;
3. isolate the elementary source-atom quadratic-normal observable as a one-parameter function of `omega`;
4. theoremize its exact endpoint zeros at `omega=0` and `omega=1`;
5. only then test the smallest source-specific inequality or factorization that could constrain the actual regular first-bad trial vector.

This maximizes information gain while avoiding a premature global sign conjecture.

## Standing question after #131

The source interface is no longer opaque. The question is now:

> What property of the **actual canonical pole/arch/prime combination, evaluated on the canonically oriented first-bad trial vector and composed with the parity overlap**, is incompatible with the regular or resonant branch?

That is the immediate E4-A4 problem.

**RH remains OPEN.**
