# Post-#184 research delta — Hermitian log drift and remainder domination

> **Claim firewall: RH remains OPEN.**
>
> This document is the Post-Green Research Pass for merged-green theorem PR #184. It separates exact theorem authority, derived consequences, research hypotheses and finite falsification targets.

## Exact authority object

```text
PR = #184
validated theorem head = a756494ebe7e2530715e996b9a9a341fbe07c683
merged theorem commit = 6f04e94473eb112b59eeaa2c6fc6ac6cbe7fe30e
validated theorem tree = 6c77cd470809959a403b3bcc5f08d39f4076fa4c
RHRC #1089 = SUCCESS
Permansson #862 = SUCCESS
```

The exact checked theorem object is therefore the #184 head/tree above. The merge preserves that theorem tree. Compiler/CI evidence is authoritative for the formal claims below.

## What became formally true

### PROVED — complex-Hermitian 2x2 Schur calculus

The production-facing 2x2 block may now be treated in genuine Hermitian form with complex off-diagonal coordinate `b` and correction

```text
|b|^2 / a
```

rather than silently substituting the real proxy `b^2/a`.

Lean includes real-component derivative theorems for the real and imaginary parts of the off-diagonal coordinate and contact-local determinant/pivot orientation transfer under H1.

### PROVED — full frozen parity production family on logarithmic cover

#184 theoremizes the full frozen parity family on logarithmic coordinate `t` in the exact form

```text
M~(t) = -t I + R~(t).
```

It also proves the exact fixed-cell bridge back to the actual production `parityCompressedCanonical` family and the deck-translation law.

### PROVED — N2 predecessor / canonical cubic shell geometry

For the N2/K3 microscope, #184 proves the relevant predecessor/shell reconstruction, the canonical cubic shell is nonzero, and predecessor and shell are orthogonal.

This removes the need to identify the research integer shell with the Lean canonical shell at the same magnitude.

### PROVED — algebraic universal-drift / remainder split

For derivative data of the required form, #184 proves

```text
P_t' = - envelopeNormSq + remainderEnvelopeDerivative.
```

The universal term is negative. Every possible cancellation is isolated in the remainder derivative.

### PROVED — conditional negative orientation

#184 proves

```text
remainderEnvelopeDerivative < envelopeNormSq
  -> P_t' < 0.
```

Combined with the contact calculus, this gives the exact sign mechanism that a future source-specific domination theorem would need.

## What changed

Before #184 the project still had a representation/interface question:

```text
can the real q13 contact calculus be attached safely to complex production?
```

After #184 that question is closed at the algebraic/log-cover level.

The frontier has compressed to:

```text
actual source-specific remainder derivatives
  -> quantitative remainder domination
  -> opposing first-bad contact orientation on the same state
```

The project therefore no longer needs a vague theorem saying “canonical arithmetic has the right sign.” A narrower candidate law is available:

```text
production remainder drift < universal envelope drift.
```

## Important non-upgrade

#184 does **not** yet assemble the actual source-specific real scalar derivative witnesses from the already-proved complex frozen-source remainder holomorphy.

Therefore the statement

```text
P_t' = -E + R_t'
```

is theorem authority as an algebraic derivative decomposition under the stated derivative hypotheses, but a fully instantiated production `HasDerivAt` theorem for the exact N2 scalar coordinates remains OPEN.

Likewise, #184 does not prove

```text
R_t' < E.
```

Analyticity supplies derivative existence infrastructure, not a magnitude bound.

## Upstream implications

The upstream analytic burden is smaller than it appeared before #184.

The repository already proves entrywise holomorphy of the complete frozen complex source remainder on an explicit punctured strip containing the nonzero real axis. The remaining derivative-interface work should therefore be finite-dimensional transport:

```text
complex source remainder holomorphy
  -> parity projection
  -> N2 predecessor/canonical-shell pairings
  -> scalar analyticity / real derivative witnesses
```

For N=2 the intrinsic predecessor has complex dimension one and the successor shell has complex dimension one. This makes the target derivative surface genuinely scalar once the canonical vectors are fixed.

## Downstream implications

If the actual production scalar derivatives are theoremized, #184 immediately upgrades to an actual production Schur derivative identity.

If the source-specific domination inequality is then proved at the relevant contact, the pivot derivative is forced negative.

The remaining contradiction would then require an independently proved first-bad/contact statement forcing the incompatible orientation on the exact same retained state.

This is the Pair-A same-state incompatibility route in concrete form.

## Resurrected routes

### Local contact calculus — RESURRECTED / ACTIVE

The old global Schur-monotonicity route remains quarantined, but #182/#184 establish that local contact derivative analysis is legitimate and production-compatible.

The route revived is:

```text
local contact orientation
```

not

```text
global fixed-sign Schur derivative.
```

### Existing complex source holomorphy — newly valuable upstream infrastructure

The source holomorphy modules were originally needed to legalize the complex production continuation. After #184 they also become the shortest route to the missing scalar remainder derivative witnesses.

## New RH-relevant clues

### LEAD / HYPOTHESIS — relative-speed law

The arithmetic law may be a relative derivative bound rather than a sign theorem for the arithmetic remainder itself.

In logarithmic coordinate:

```text
R_t' < E.
```

In physical aperture `L`:

```text
R_L' < E/L.
```

Equivalently:

```text
L * R_L' < E.
```

Interpretation: the universal logarithmic geometry pulls the Schur pivot downward at a known rate. The canonical remainder may push back, but FB-05 only needs to show that it cannot push back strongly enough at the forbidden state.

### LEAD / HYPOTHESIS — contact-local bound may be much weaker than global monotonicity

The inequality need not hold on every state or every aperture. A theorem restricted to the retained first-bad/contact hypotheses could be sufficient and would avoid the known sign-changing behavior that killed global Schur monotonicity.

### LEAD / HYPOTHESIS — the N2 microscope may expose the right invariant

Because the q13/N2/K3 state is the sharpest finite near-contact laboratory and #184 now supplies the exact canonical shell geometry, the finite decomposition may reveal which production remainder component or cancellation identity deserves theorem investment.

This remains a lead until generalized to the arbitrary retained first-bad state.

## Falsification checks

### 1. Coordinate mismatch

#184 uses `t=log L`, while #178/#180 differentiates in physical `L`.

Never compare

```text
R_t'
```

directly to a physical-`L` derivative.

Use

```text
P_L' = -E/L + R_L'.
```

### 2. Direct finite falsifier

Reuse the exact frozen #180 schedule and evaluate/enclose

```text
E
P_L'
R_L' = P_L' + E/L
margin = E/L - R_L'
ratio = L*R_L'/E.
```

If `ratio >= 1` on a legitimate state, the simple domination law fails in that scope.

### 3. Analyticity is not a bound

A proof that jumps from holomorphy to a small derivative without a quantitative estimate is invalid.

### 4. q13 is not arbitrary first-bad coverage

A positive domination margin on the frozen q13/Q14 microscope is research evidence only until the theorem hypotheses are generalized to the exact arbitrary retained first-bad state.

### 5. Same-state firewall

A negative production contact orientation is useful only if the opposing first-bad orientation applies to the same state, aperture, parity, normalization and production object.

### 6. Global monotonicity firewall

A local negative derivative theorem must not be rewritten into a global fixed-sign Schur derivative claim. DR-022 remains quarantined.

## Highest-leverage next moves

1. **Research first:** add a post-#184 R003 falsification pass on the exact frozen #180 states that separates `-E/L` from the production remainder derivative and reports the domination margin/ratio.
2. **If the signal survives:** theoremize the actual N2 production remainder scalar derivative witnesses from the existing complex remainder holomorphy.
3. **Then:** instantiate #184 as an actual production `HasDerivAt` Schur identity.
4. **Then:** prove or falsify a source-specific contact-local domination theorem.
5. **In parallel:** identify and theoremize the first-bad/contact orientation required for contradiction on the exact same retained state.
6. **Only after both sides exist:** compose them into FB-05/FB-06 exclusion.

## Standing questions

> Given everything now formally true, what becomes possible that was not possible before?

The project can now ask one scalar quantitative question about the production remainder rather than another broad representation/sign question.

> If this contains a clue toward RH, where does it propagate?

Upstream into source-specific derivative estimates; downstream into same-state contact orientation and then negative-root exclusion.

> What experiment or lemma most efficiently tells us whether the clue is real?

The exact #180-schedule decomposition

```text
ratio = L*R_L'/E
```

is the fastest falsifier. If it stays decisively below one at the dangerous states, the theorem target becomes concrete. If it fails, the route should be revised before more Lean work.

**RH remains OPEN.**
