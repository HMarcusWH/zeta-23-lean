# Post-#224 obstruction-ledger delta

## Authority

- theorem authority: PR #224
- validated/final head: \`83de9193dffba12097d950d2291348db76d047f7\`
- merge: \`0f8f5ad468b337622942f76725c9d76db74e27e4\`
- tree: \`aaedc131612393a1198837b3e5288e48538a94ae\`
- latest rigorous bounded research evidence: PR #223
- control-semantic authority: PR #117
- terminal claim: **RH remains OPEN**

## OBS-059I — current state

Status:

\`\`\`text
OPEN / BIREGULAR-SCALARIZED /
CUBIC-PROJECTION CLOSED /
PREDECESSOR-CORRECTION PROPORTIONALITY REQUIRED /
CANONICAL-ARITHMETIC INCOMPATIBILITY STILL REQUIRED
\`\`\`

### Closed by #224

**PROVED**

\`\`\`text
d^3 - g_K = ((3*K^2 + 3*K - 1)/5) * d
\`\`\`

Exact declaration:
\`cubicProjectionResidual_eq_oddCubicProjectionSlope_smul\`.

This closes the explicit cubic-projection coefficient that had remained qualitative since the earlier cubic-shell incidence stage.

### Immediate open theorem

**OPEN / NEXT**

\`\`\`text
oddCubicGeneratorPredecessorPart N
  = -((2*N - 1)/6) * oddIndexCubicShellPredecessorPart N
\`\`\`

This theorem was advertised by the #224 search but is not in the merged Lean declaration surface.

### Conditional consequences

If the open theorem above is proved:

**DERIVED / NOT FORMALIZED**

\`\`\`text
Gamma0 = 1 + ((2*N - 1)/6)*(1 - alpha0)

6*Gamma0 + (2*N - 1)*alpha0 = 2*N + 5

6*sigmaMinus
  = alpha0*(6*sigmaPlus - (2*N - 1)*mu0)
    + (2*N + 5)*mu0
\`\`\`

These consequences do not close OBS-059I by themselves.

## Remaining closure obligations

\`\`\`text
selected-even predecessor correction proportionality        OPEN / NEXT
selected-even alpha/Gamma affine relation                  DERIVED CONDITIONAL / NOT FORMALIZED
selected-even one-coefficient zero-shift scalar            DERIVED CONDITIONAL / NOT FORMALIZED
canonical simultaneous odd-bad exclusion                   OPEN
odd-selected first-bad branch                              OPEN
parity-complete retained-state impossibility               OPEN
negative-root exclusion                                    OPEN / STRONGER HISTORICAL ROUTE
open-strip carrier -> exact Mathlib RiemannHypothesis      OPEN TERMINAL SEAM
OBS-059I                                                   OPEN
RiemannHypothesis                                          OPEN
\`\`\`

## Scope firewall

The #205 synthetic countermodel already uses the repository's parity spaces, centered predecessor embedding, reversal symmetry and intrinsic shell geometry but is not canonically realizable. Therefore a geometry-only proportionality may compress the state without excluding simultaneous badness.

The #215 full-carrier audit already falsifies universal arbitrary-vector complete-source/M4 sign and proportionality. Any terminal sign law must therefore spend retained-state or canonical arithmetic information not present in that audit.

The selected-even scalar theorem is not a WLOG reduction. A complete finite contradiction must also account for the odd-selected branch or prove a parity-symmetric alternative.

The strong theorem

\`\`\`lean
IsEmpty (BiRegularCellMinimalNegativeEnergyCertificate Q)
\`\`\`

is sufficient but not logically necessary. A contradiction specialized to the off-line-zero-generated retained certificate is enough for the zeta route.

**Supporting lemma != retained-state contradiction. Retained-state contradiction != exact Mathlib RH until the terminal strip/trivial-zero seam is formalized. RH remains OPEN.**
