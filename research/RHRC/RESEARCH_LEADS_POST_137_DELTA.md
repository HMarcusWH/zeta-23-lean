# RHRC Post-Green Research Pass — PR #137

> **Claim firewall: RH remains OPEN.**
>
> This is a post-green research delta, not a proof, claim promotion, or terminal RH statement.

## Exact authority

```text
PR = #137 FIRST-BAD-RIGIDITY-E4-A4b2a: canonical one-step determinant reduction
validated theorem head = 64988e142590c82bd0ad43604279ede9a8e85eff
validated theorem tree = e3de4dc0377f0124832822b6f97ab5bbd7718640
merge = fa2f209a6eb8b4059968e8d61239d80588ca256c
merged main tree = e3de4dc0377f0124832822b6f97ab5bbd7718640
RHRC #878 = SUCCESS
Permansson #651 = SUCCESS
control semantic anchor = PR #117
RH = OPEN
```

The exact #137 head passed `lake build Zeta23.CCM`, `lake build Zeta23.ExceptionalZero`, the no-sorry/project-axiom scan, RHRC regression/source-normalization gates, the Control-v2 real-history smoke run, and Permansson verification.

## What became formally true

### PROVED — exact source pairing

The canonical production source now has an exact complex pairing interface, not only a self-energy or linear normal moment. This makes the shell/predecessor cross term theorem-addressable through the same pole/arch/scalar/prime source.

### PROVED — exact one-step energies and determinant

For parity `p`, predecessor block `A`, canonical cubic shell `c`, and predecessor vector `w`:

```text
q_A(w) = intrinsicPredecessorRealEnergy p L N w
b(w)   = cubicShellCoupling p L N w
q_c    = cubicShellRealEnergy p L N
Δ(w)   = q_c*q_A(w) - |b(w)|^2.
```

Lean proves exact production-channel formulas for these objects.

### PROVED — kernel annihilation from determinant nonnegativity

If `Az=0` and `Δ(z)>=0`, then `b(z)=0`. This is denominator-free and uses no pseudoinverse.

### PROVED — conditional zero-shift regularity and endpoint sign

`canonicalOneStepDomination` is defined as

```text
q_c >= 0
AND
forall w, Δ(w) >= 0.
```

If it holds, the shell coupling annihilates `ker A`, lies in `range A`, and admits a zero-shift preimage. With predecessor nonnegativity, the regular zero-shift endpoint satisfies `Re S0>=0`.

### PROVED — conditional negative-root exclusion

Under predecessor nonnegativity and `canonicalOneStepDomination`, the explicit cubic Schur scalar has no safe negative root.

This is conditional. No theorem asserts the domination certificate.

### PROVED — exact domination-failure disjunction

```text
not canonicalOneStepDomination
  <-> q_c < 0 OR exists w, Δ(w) < 0.
```

### PROVED — global off-line-zero countercertificate

A hypothetical off-line zeta zero forces one global-first-bad predecessor-nonnegative canonical state where domination fails, and therefore forces

```text
q_c < 0 OR exists w, Δ(w) < 0.
```

No RH theorem follows unless both alternatives are excluded by new mathematics.

## What changed

Before #136/#137, the route still needed the scalar-sensitive energy object and a proof that the proposed one-step inequality was actually sufficient to remove resonance and contradict the negative endpoint.

After #136/#137:

```text
absolute source energy                PROVED
complex source pairing                PROVED
one-step determinant                  PROVED
domination sufficiency                PROVED
global domination-failure endpoint    PROVED
```

The open content is no longer proof plumbing. It is the arithmetic sign theorem itself.

The strongest conceptual change is that an off-line zero now forces a **finite sign countercertificate** in the exact canonical source: negative shell energy or negative one-step determinant.

## Upstream implications

### DERIVED — unify self-energy and cross-energy at the source-pairing level

The #136 energy and #137 pairing should be treated as one bilinear/Hermitian source interface. Future algebra should avoid separately expanding `q_c`, `q_A`, and `b` if a single pairing-level representation can produce all three.

### LEAD — search for a positive measure / Gram representation

If the full canonical source pairing can be rewritten as an integral or sum of squares with a positive measure/kernel on the legal first-bad carrier, then `Δ` may become a direct Cauchy-Schwarz remainder.

This is a lead, not a result. The Weil source is not globally positive without RH-strength input, so any such representation must be carefully scoped to the finite first-bad carrier and cannot smuggle in the desired conclusion.

### DERIVED — kernel directions are the sharp resonance test

On `Az=0`,

```text
Δ(z) = -|b(z)|^2.
```

Thus determinant nonnegativity on the kernel is exactly coupling annihilation. This makes kernel vectors a high-value falsification surface for any proposed arithmetic estimate.

### DERIVED — homogeneity reduces the search geometry

Both `q_A(w)` and `|b(w)|^2` scale quadratically in `w`, so the determinant sign is homogeneous in the predecessor vector. Numerical/symbolic falsification can therefore normalize `w` without loss, provided the normalization is applied on the exact legal carrier.

## Downstream implications

### If the two canonical signs are proved

If, under the exact first-bad-compatible hypotheses, Lean proves

```text
q_c >= 0
forall w, Δ(w) >= 0,
```

then #137 supplies the contradiction immediately: the same state forced by an off-line zero both fails and satisfies domination.

The existing global off-line-zero reduction would then rule out off-line zeros. An explicit terminal theorem bridge to Mathlib's `RiemannHypothesis` statement would still need to be written and validated before any RH claim.

### What #137 does not solve

It does not provide a generic finite-to-infinite determinant convergence theorem, a source positivity theorem, a zeta spectral determinant theorem, or a new RH equivalence. It sharpens the current finite first-bad route.

## Resurrected routes

### RESURRECTED AS A SMALLER TARGET — source-coordinate cancellation

The post-#132 `omega^7 / omega^9` boundary-flat cancellation signal was previously a possible ingredient for absolute energy. #136 built the energy and #137 built the determinant, so the useful question is now sharper:

> do those cancellations control the **full determinant remainder** strongly enough to force `Δ>=0`?

This route is worth rerunning in that form.

### WEAKENED NEED — regular-aperture log-lift

A4R remains mathematically legitimate, but #137 reduces its leverage. If domination is proved, resonance is removed directly. A4R is now useful only if injective predecessors materially simplify the arithmetic sign proof.

### STILL DEAD — factorwise transfer closure

Nothing in #136/#137 revives division by `alpha`, `Gamma`, overlap or source moment. The new route avoids those factors entirely.

### STILL DEAD — generic structural exclusion

#137 itself shows the missing input is a sign of the actual canonical source. Generic Hermitian/parity/KKT structure remains insufficient.

## New RH-relevant clues

### LEAD / HYPOTHESIS — determinant as Cauchy-Schwarz remainder

Because

```text
Δ = q_c q_A - |b|^2,
```

the formal shape is exactly a 2x2 Gram determinant. If `q_c`, `q_A`, and `b` can be realized as norms/pairings in one genuinely positive auxiliary space constructed from the canonical arithmetic source, nonnegativity would follow from Cauchy-Schwarz.

The key word is **genuinely positive**. Building that auxiliary space may itself require RH-strength positivity, which would make the route circular.

### LEAD / HYPOTHESIS — attack the counterexample space

Instead of proving `Δ>=0` directly for all states, classify what `Δ<0` forces in the pole/arch/prime channels. A negative determinant may require an extreme imbalance among source channels that is incompatible with first-bad minimality, boundary-flat moments, or the exact finite von-Mangoldt structure.

This is potentially more informative than a direct inequality proof because it attacks the countercertificate space produced by #137.

### LEAD / HYPOTHESIS — finite source-pairing minors

The determinant is a principal 2x2 minor of the one-step Hermitian form along `span{w,c}`. It may be useful to prove positivity for a generating family of predecessor directions and then extend by a source-specific convexity or basis theorem. No such reduction is currently proved.

## Falsification checks

1. **Canonical low-dimensional search.** Search exact or rigorously enclosed canonical matrices for predecessor-nonnegative states with `q_c<0` or `Δ<0`. Do not use legacy `finiteMatrix` absolute signs.
2. **Kernel stress.** Search kernel/near-kernel predecessor directions first; they are the sharpest test of coupling annihilation.
3. **Atom-indefiniteness check.** Any proof based on termwise nonnegative prime/arch/pole atoms should be rejected unless the exact legal hypotheses change the sign analysis; individual source atoms are not generically positive.
4. **Circularity check.** A proposed positive Gram representation must not assume Weil positivity, RH, absence of the negative successor root, or another equivalent statement.
5. **Normalization check.** The argument must fail under arbitrary scalar shifts `M+tI`; otherwise it is probably still blind to the canonical spectral origin.
6. **Parity check.** Both parity branches must be handled by the source theorem or by a proved reduction eliminating one branch.
7. **First-bad relevance check.** A random canonical sign failure outside the predecessor-nonnegative/global-first-bad hypotheses may refute an overbroad theorem but not the scoped route.
8. **Scaling check.** Normalize `w` in experiments to avoid mistaking trivial amplitude scaling for determinant structure.

## Highest-leverage next moves

1. **Build an exact symbolic decomposition of `Δ(w)`** from `canonicalSourceChannelPairing` and `canonicalSourceChannelEnergy`, simplifying all cancellations before inequalities.
2. **Run a bounded canonical falsifier** on the smallest legal/predecessor-nonnegative states. Information gain is maximal: one genuine sign failure immediately redirects the route.
3. **Attempt a pairing-level Gram/integral representation** rather than separate termwise inequalities.
4. **Retarget the high-order source-coordinate expansion** to the determinant and shell energy.
5. **Only then formalize the surviving inequality mechanism** in Lean.

## Standing questions

**Given everything now formally true, what becomes possible that was not possible before?**  
A hypothetical off-line zero can now be attacked through a concrete finite sign-failure witness in the actual canonical source rather than through generic branch language.

**If this contains a clue toward RH, where does it propagate?**  
Upstream it points to the source pairing and possible positive representations; downstream a sign theorem plugs directly into the #137 global contradiction wrapper.

**What experiment or lemma most efficiently tells us whether the clue is real?**  
A low-dimensional exact canonical search for `q_c<0` or `Δ<0`, followed—if it survives—by a symbolic full-channel decomposition looking for a non-circular Gram/Cauchy-Schwarz structure.

**RH remains OPEN.**
