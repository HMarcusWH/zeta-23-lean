# Post-#224 cubic-projection research delta

## Exact authority

- PR: #224
- validated/final head: `83de9193dffba12097d950d2291348db76d047f7`
- merge: `0f8f5ad468b337622942f76725c9d76db74e27e4`
- tree: `aaedc131612393a1198837b3e5288e48538a94ae`
- exact promoted declaration: `Zeta23.CCM.cubicProjectionResidual_eq_oddCubicProjectionSlope_smul`
- terminal claim: **RH remains OPEN**

# What became formally true

**PROVED.** For `K >= 1`, the residual between the centered cubic power vector and the constrained odd cubic compression is exactly one-dimensional with explicit slope
[
d^3-g_K = rac{3K^2+3K-1}{5},d.
]

This strengthens the pre-#224 statement that the residual merely lies in `span{d}`.

**NOT PROVED BY #224.** PR #224 does not establish
[
a_N=-rac{2N-1}{6}d_N,
]
where `a_N = oddCubicGeneratorPredecessorPart N` and
`d_N = oddIndexCubicShellPredecessorPart N`.

# What changed

The cubic correction geometry is no longer only qualitative. The coefficient is now exact and theorem-backed, so the next proof attempt should consume this closed form rather than repeat finite-coordinate discovery.

The theorem authority advances to #224, while the latest rigorous bounded research evidence remains #223 and the control-semantic anchor remains #117.

# Upstream implications

The exact coefficient is the ratio of the centered fourth and second moments on the symmetric discrete grid. This supports viewing `oddCubicCompressionVector` as a discrete Gram-Schmidt projection of (d^3) against (d).

**LEAD / HYPOTHESIS.** The parity-shell hierarchy may admit a discrete orthogonal-polynomial connection calculus. This is not theorem authority.

# Downstream implications

The immediate theorem target is the predecessor-correction proportionality
[
a_N=-kappa_N d_N,qquad
kappa_N=rac{2N-1}{6}.
]

For Lean, define (kappa_N) in (mathbb C):
```lean
def crossParityCubicCorrectionKappa (N : ℕ) : ℂ :=
  (2 * (N : ℂ) - 1) / 6
```
so that no `Nat.sub` or natural-number division ambiguity can enter the proof.

If this theorem is proved, then **DERIVED / NOT YET FORMALIZED**
[
Gamma_0=1+kappa_N(1-alpha_0),
]
equivalently
[
6Gamma_0+(2N-1)alpha_0=2N+5,
]
and therefore
[
6sigma_-=
alpha_0igl(6sigma_+-(2N-1)mu_0igr)+(2N+5)mu_0.
]

# Resurrected routes

The large-aperture route remains worth reconsidering after scalar compression because an off-line zero generates finite badness for all sufficiently large apertures. Once the retained state has fewer free coefficients, a bounded-(N_*(L)) versus (N_*(L)	oinfty) dichotomy may expose new canonical arithmetic rigidity.

Pair B remains independent and secondary; it was deprioritized, not falsified.

# New RH-relevant clues

**LEAD / HYPOTHESIS.** The exact #224 slope and the experimentally reconstructed predecessor ratio may be adjacent connection coefficients in a discrete orthogonal-polynomial hierarchy.

**LEAD / HYPOTHESIS.** The terminal contradiction is more likely to constrain the complete collapsed scalar combination than to provide independent signs for (alpha_0,Gamma_0,mu_0,sigma_+). Historical failures repeatedly show that factorwise enclosure destroys useful canonical correlation.

# Falsification checks

1. Test every geometry-only consequence against the #205 synthetic Pair-D countermodel. If it survives, it is compression rather than exclusion.
2. Do not revive universal full-carrier source/M4 sign or proportionality; #215 already falsified those formulations on the tested carrier.
3. Any retained-state sign law must use hypotheses absent from #205/#215, such as canonical-source arithmetic, first-bad ancestry, cell minimality, or aperture structure.
4. The selected-even zero-shift theorem is not parity-complete. The odd-selected first-bad branch remains OPEN.
5. Do not treat the PR #224 title/body as authority beyond the exact compiled declaration.

# Highest-leverage next moves

1. Prove
   ```lean
   oddCubicGeneratorPredecessorPart N =
     -(crossParityCubicCorrectionKappa N) •
       oddIndexCubicShellPredecessorPart N
   ```
   for `1 ≤ N`.
2. Immediately formalize the (alpha_0/Gamma_0) affine relation.
3. Immediately formalize the one-coefficient selected-even scalar normal form.
4. Re-compose the accumulated canonical source/Riesz/kernel/aperture theorem inventory against the **whole** collapsed scalar expression.
5. Keep the terminal retained-state theorem parity-complete.
6. Separately close the final seam from the project's open-strip zero carrier to Mathlib's exact `RiemannHypothesis`.

# Standing questions

Given everything that is now formally true, what becomes possible that was not possible before?

The exact cubic projection coefficient is now available as a theorem input, so the predecessor-correction relation can be attacked symbolically rather than discovered numerically.

If this contains a clue toward RH, where does that clue propagate upstream or downstream through the existing mathematics?

Downstream it compresses the cross-parity zero-shift transfer. Upstream it suggests a more canonical polynomial basis for the shell geometry.

What experiment, lemma, reformulation, or connection would most efficiently tell us whether that clue is real?

The fastest discriminator is the exact predecessor-correction theorem itself, followed immediately by testing whether its consequences eliminate any state beyond the generic #205 geometry.

**OBS-059I remains OPEN. Odd-selected closure remains OPEN. Parity-complete retained-state exclusion remains OPEN. RH remains OPEN.**
