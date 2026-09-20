# Post-#229 research leads delta — Riesz representation to source coupling

> **Claim firewall: RH remains OPEN.**
>
> Exact theorem authority: PR #229, head `9d4f81c171264be424fbac40f1211263c3cc6abd`,
> merge `992398c810de5fb84919846fc4192d709d51e783`, tree
> `d9ae07d1ca92cb23b4a3ae3ccae0b32e9b7d38c8`.

## What became formally true

**PROVED.** The safe odd correction functional has the generic representation
`chi(y) = <R b,y>/<c,c>`.

**PROVED.** The remaining alpha and Gamma corrections are evaluations of the
same Riesz representative:
`1-alpha = <R b,d>/<c,c>` and
`1-Gamma = <R b,a>/<c,c>`.

The existing Gamma overlap theorem was refactored through this generic result
without changing its public statement. Alpha reality/sign, source coupling,
branch exclusion, negative-root exclusion, and RH were not proved.

## Workflow harvest

All 13 jobs attached to the validated #229 head completed successfully.
The formal Lean/RHRC gate built CCM and ExceptionalZero and rejected forbidden
placeholders. The post-190/192/194/196/198/200/202/214/222 and Permansson
workflows replayed their prior dispositions without theorem promotion.
A green replay preserves a result; it does not create new theorem authority.

## What changed

The last free cross-parity coefficient is no longer an opaque scalar. It is an
exact mixed resolvent pairing with one canonical Riesz vector.

## Upstream implications

The Riesz theorem is the smaller canonical statement beneath the previous
Gamma-specific overlap calculation. Future coefficient identities should
factor through it instead of rebuilding quotient/symmetry algebra.

## Downstream implications

By resolvent symmetry and conjugate symmetry, the #229 alpha numerator is
naturally routed toward the existing shell coupling on the special direction
`R d`. The next theorem target is
`CROSS_PARITY_CORRECTION_SOURCE_COUPLING`, followed by a production-channel
rewrite and a retained source-balance identity.

These implications are **DERIVED / NEXT**, not yet Lean theorem authority.

## Resurrected routes

The one-step source/Gram architecture becomes relevant on the distinguished
`R d` direction. This does not resurrect the falsified universal full-carrier
sign/proportionality route from post-#215.

## New RH-relevant clues

**LEAD.** The mixed coefficient may be expressible exactly as
`star (1-alpha) * <c,c> = cubicShellCoupling (R d)`, hence through the
production canonical source-channel pairing. Combining that with retained
secular completion may reduce the odd-good branch to an exact scalar
source-balance before any sign theorem is attempted.

## Falsification checks

Same-vector resolvent positivity does not control the mixed pairing. Alpha is
not proved real or positive. Generic full-carrier source/M4 sign and
proportionality remain falsified at their tested scope. The good-sector to
2x2 Gram-domination bridge is not yet theoremized. Selected-even is not WLOG,
the simultaneous odd-bad branch remains open, and PR #223 still has zero
qualified retained audit points.

## Highest-leverage next moves

1. Formalize the alpha-to-`cubicShellCoupling (R d)` identity.
2. Rewrite the coupling through `canonicalSourceChannelPairing`.
3. Derive the retained source balance first under an explicit nonzero source
   moment, then obtain odd-good as a corollary.
4. Only after that, formalize good-sector PSD to one-step Gram domination.
5. Preserve all parity-complete and terminal RH firewalls.
