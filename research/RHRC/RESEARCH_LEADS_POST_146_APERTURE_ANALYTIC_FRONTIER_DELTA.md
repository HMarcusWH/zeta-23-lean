# Research leads delta — post-#146 aperture analytic frontier

Date: 2026-09-11  
Status: **current research-priority delta**  
Claim firewall: **RH remains OPEN.**

This delta supersedes the post-#142 delta for current execution priority. Older deltas remain historical evidence and should not be rewritten to look current.

## Exact validated state

```text
merged theorem anchor = PR #146
merge commit = f2999d12e29d61debce130e83491ac3df410b0c2
merged tree = fe76581d445569cb838cb4df7bf50703aa34f5cc
validated theorem head = a25d238478f7b19072c5364486b8f3f994bf6b79
validated theorem tree = fe76581d445569cb838cb4df7bf50703aa34f5cc
RHRC #922 / run 34600323163 = SUCCESS
Permansson #695 / run 34600323144 = SUCCESS
control semantic anchor = PR #117
terminal claim = RH_OPEN
```

The #146 PR head and merged-main commit have the same tree. The authoritative RHRC run succeeded across the research/control suite, normalization/source firewalls, aggregate `Zeta23.CCM` and `Zeta23.ExceptionalZero` builds, and forbidden placeholder/project-axiom scan. Permansson independent verification also succeeded.

## What became formally true

### PROVED before #144 and still load-bearing

The project already had:

```text
off-line zero
-> finite canonical negative obstruction
-> every sufficiently large aperture has a finite negative canonical witness   #140
-> fixed-cell actual-source continuity                                        #142
-> same finite size and same vector remain negative on an open in-cell set    #142
-> predecessor regular <-> predecessor injective                              #140
-> regular predecessor -> unique zero-shift preimage                          #140.
```

### PROVED / #144 — exact frozen production and log-cover scaffold

PR #144 constructs the exact frozen production source and carries the real scalar split through the actual parity/intrinsic projections.

The exact theorem-backed chain includes:

```text
frozenCanonicalSourceMatrix_eq_canonicalSourceMatrix_fixedCell
frozenCanonicalSourceMatrix_eq_neg_log_identity_add_remainder
frozenParityCompressedCanonical_eq_actual_fixedCell
frozenIntrinsicPredecessorBlock_eq_actual_fixedCell
frozenParityCompressedCanonical_eq_neg_log_id_add_remainder
frozenIntrinsicPredecessorBlock_eq_neg_log_id_add_remainder
intrinsicPredecessorBlock_eq_neg_log_id_add_remainder_fixedCell
complexFrozenParityCompressedRemainder_ofReal
complexFrozenIntrinsicPredecessorRemainder_ofReal
liftedFrozenIntrinsicPredecessorRemainder_add_two_pi_I
liftedFrozenIntrinsicPredecessorBlock_add_two_pi_I
liftedFrozenIntrinsicPredecessorBlock_of_log_fixedCell
```

So the route now has an exact logarithmic-cover object

```text
Ahat(z) = -z I + R(exp z)
```

where `R(exp z)` is exactly deck-periodic and `Ahat(log L)` recovers the actual production intrinsic predecessor on a physical cutoff cell.

This is an algebraic/production/log-cover theorem package. It is **not** yet a theorem that `R` is holomorphic in the complex aperture parameter.

### PROVED / #145 — removable scalar analyticity

The scalar layer now has a theoremized removable extension:

```text
complexApertureScalarFactorRemovable 0 = 2
complexArchExpSlope is eventually nonzero near 0
complexApertureScalarFactorRemovable is AnalyticAt at 0
its value at 0 lies in Complex.slitPlane
Complex.log of the removable factor is AnalyticAt at 0
complexApertureScalarRemainderRemovable is AnalyticAt at 0.
```

The analyticity theorem is intentionally local. The divided exponential slope has nonzero zeros at `2*pi*i*k`, `k != 0`, so no global-entire quotient statement is available.

### PROVED / #146 — removable scalar equals production scalar

PR #146 closes the production bridge:

```text
z != 0
-> complexApertureScalarFactorRemovable z
   = complexApertureScalarFactor z

z != 0
-> complexApertureScalarRemainderRemovable z
   = complexApertureScalarRemainder z

L > 0
-> removable factor/remainder at ofReal L
   = exact production real formulas.
```

The proof explicitly splits the case `exp z - 1 = 0`; it does not assume global denominator nonvanishing.

## What changed

The old A4R1b problem statement bundled together several logically distinct obligations:

```text
construct complex production continuation
+ isolate logarithmic scalar
+ obtain log-cover/deck structure
+ prove holomorphy
+ prove determinant nonidentity
+ obtain dense regularity.
```

After #144-#146, the first three are now theorem-backed and the scalar removable point is repaired and bridged to production.

Therefore the first live break is no longer "construct the analytic frozen predecessor" in the broad sense. It is specifically:

```text
prove genuine complex parameter analyticity of the exact fixed-unit production source integrals
-> assemble genuine holomorphy of the frozen source/predecessor remainder.
```

This is a meaningful compression of the dependency graph: algebraic continuation and analytic regularity are now separate gates.

## Upstream implications

1. **Do not modify theorem-locked production definitions to bake in the removable repair.** #146 already proves the bridge. The production objects remain the authority.
2. **The scalar point singularity should be removed from the list of analytic blockers.** It is now theorem-backed as removable and tied to production.
3. **The exact complex source cores should be treated as the canonical upstream analytic interface.** The next theorem should attach analyticity to those existing definitions rather than introduce a parallel surrogate family.
4. **A reusable parameter-integral lemma may compress several proofs.** If `complexAlphaCore`, `complexBetaCore` and `complexGammaCore` share a common fixed-domain/dominated-differentiation pattern, prove the smallest canonical abstraction that captures it without obscuring source normalization.
5. **Keep the domain local enough to avoid false global zero-free claims.** The scalar analysis already demonstrates why global denominator nonvanishing is unsafe.

## Downstream implications

If the exact complex frozen intrinsic predecessor remainder is proved holomorphic on an appropriate connected domain, the #144 deck architecture becomes available for determinant analysis without inventing a new continuation object.

The intended downstream composition is:

```text
#142 open interval J of fixed-witness negativity
+
holomorphic lifted predecessor determinant
+
determinant not identically zero
-> singular apertures cannot fill J
-> choose a regular aperture inside J
-> same negative witness survives at a regular predecessor.
```

This is the practical reason holomorphy matters: it may convert #142 open witness persistence into a regular negative-state selection.

However:

```text
holomorphic determinant != determinant nonidentity
regular negative state != contradiction.
```

The determinant theorem and the final arithmetic sign remain separate obligations.

## Resurrected routes

### Resurrected: finite-dimensional logarithmic-cover determinant argument

The monodromy/spectral-counting idea is now better posed than it was before #144 because the exact lifted production object and deck identities are theorem-backed.

Classification: **LEAD / HYPOTHESIS, worth pursuing after holomorphy.**

Remaining blockers:

```text
genuine holomorphy of the remainder/determinant
determinant nonidentity proof on the exact finite-dimensional operator
correct connected domain / identity-theorem hypotheses.
```

### Not resurrected: translation identity as a holomorphy shortcut

The generic `-z+Re z` countermodel blocks this permanently unless a genuinely new analytic premise is added.

### Still fallback: all-size Baire / finite-prefix simultaneous regularization

The post-#142 cell-minimal composition remains smaller. Return to all-size/Baire machinery only if the cell-minimal route fails for a theoremized reason.

## New RH-relevant clues

### LEAD / HYPOTHESIS — open negativity plus isolated singularity set may force a regular bad state

Assume the relevant determinant is holomorphic and not identically zero. Then its zero set is locally discrete in one complex variable under the usual connected-domain hypotheses. The #142 bad witness persists on an open real interval. A discrete singular set cannot occupy that whole interval, so one should be able to select a regular point without moving the finite size or witness.

This would remove predecessor resonance from the selected bad state while preserving negativity.

It is not yet a contradiction and does not prove RH.

### LEAD / HYPOTHESIS — proof-engineering friction suggests the parameter integral is the canonical analytic bottleneck

#144-#146 repeatedly succeeded by isolating exact production algebra first and refusing to infer analytic properties from structural identities. That suggests the next high-information theorem is not another wrapper but a genuine dominated-differentiation theorem for the simplest production core.

If one core can be proved analytic with a reusable local majorant pattern, the remaining analytic layer may compress rapidly.

## Falsification checks

### Check 1 — translation/deck identities are insufficient

Countermodel:

```text
F(z) = -z + Re z.
```

For pure imaginary deck translation `T=2*pi*i`,

```text
F(z+T)=F(z)-T,
```

because `Re(z+T)=Re z`. Yet `Re z` is not complex differentiable, so `F` is not holomorphic.

Conclusion: the exact #144 deck law cannot replace a genuine analytic proof.

### Check 2 — scalar removable quotient is not globally entire

`complexArchExpSlope` vanishes at the nonzero points `2*pi*i*k`, `k!=0`. Therefore the quotient representation used for the removable scalar extension has genuine nonzero denominator zeros. Any theorem must use a local zero-free neighborhood or explicitly handle punctured-domain equality as #146 does.

### Check 3 — holomorphy does not imply nonidentity

A holomorphic determinant may vanish identically. The finite-spectrum/deck argument must separately prove nonidentity.

### Check 4 — dense regularity does not produce the arithmetic sign

The post-#142 generic regularization countermodel already shows regular positive predecessors and persistent negative successors can coexist in a generic analytic family. Actual canonical arithmetic remains essential.

### Check 5 — no hidden RH-strength premise

Any parameter-integral theorem should use ordinary local complex analysis and domination estimates from the explicit production integrands. If the proof requires a positivity or zero restriction already equivalent to successor PSD/RH, the route has become circular.

## Highest-leverage next moves

1. **Inventory exact definitions of `complexAlphaCore`, `complexBetaCore`, `complexGammaCore` and their denominators.** Identify the smallest core with the least singular structure.
2. **Prototype `complexBetaCore` holomorphy.** Prove local denominator nonvanishing and an explicit integrable majorant on the fixed interval.
3. **Extract only the reusable abstraction forced by the proof.** Do not generalize prematurely.
4. **Reuse the successful pattern for the other cores.** Preserve exact production normalization and positive-real bridges.
5. **Assemble `complexFrozenCanonicalSourceRemainder` and `complexFrozenIntrinsicPredecessorRemainder` holomorphy.** Projections are fixed finite-dimensional linear maps, so this should be algebraic once entry/core analyticity is available.
6. **Only then attack determinant nonidentity.** Use the exact theorem-backed deck shift, not an informal monodromy slogan.
7. **If nonidentity closes, derive dense regularity and immediately compose with #142 persistent negativity.** This is where the analytic work becomes a new finite regular bad-state theorem.
8. **Then return to the decisive arithmetic sign.** The regularization route is a selection mechanism, not the final positivity argument.

## Standing questions after #146

### Given everything that is now formally true, what becomes possible that was not possible before?

The project can now attack genuine parameter holomorphy directly on an exact production complex family whose real-axis provenance, intrinsic projection, scalar split and log-cover deck structure are already theorem-locked. Before #144-#146, those interfaces were themselves part of the uncertainty.

### If this contains a clue toward RH, where does it propagate?

The clue propagates downstream through determinant nonidentity and dense regularity into #142's open persistent-negative interval. If successful, it produces a regular negative first-bad state where the zero-shift preimage is unique and the Schur-energy obstruction is sharply exposed.

### What experiment, lemma, reformulation or connection most efficiently tests whether the clue is real?

A single compiler-green parameter-integral analyticity theorem for `complexBetaCore`, with explicit local domination and no normalization changes, is the best next information-gain test. If that proof pattern fails for a structural reason, it will reveal the true analytic obstruction before the project invests in determinant machinery.

## Claim firewall

Nothing in #144, #145 or #146 proves determinant nonidentity, dense regularity, the final canonical arithmetic sign, negative-root exclusion or RH.

**RH remains OPEN.**
