# Post-#157 research delta — production Riesz closure and arithmetic frontier

Date: 2026-09-13

> **Claim firewall:** compiler/CI evidence is authoritative for theorem validity. Derived formulas, numerical diagnostics and research leads are not silently promoted. **RH remains OPEN.**

## Exact authority

```text
merged main after #157 = e304f07c9e83165ebf066db0d67c2cc24f8961c2
merged theorem tree = 706dfde7f9e7b0b8403a671769d424ac7862f5e7
validated #157 head = 4b517db1d4a50277d325e77e771a30fc0db5c777
validated theorem tree = 706dfde7f9e7b0b8403a671769d424ac7862f5e7
RHRC #1017 / run 34731682546 = SUCCESS
Permansson #790 / run 34731682544 = SUCCESS
control-plane semantic anchor = PR #117
RH = OPEN
```

The validated PR head and merged main are distinct commits that share the same theorem tree.

# What became formally true

## FB-03E — genuine complex production D transport

**PROVED / #157**

The source-coordinate second derivative is theoremized on the genuine complex production energy. The proof explicitly decomposes the Hermitian quadratic energy into real and imaginary contractions and only removes the rank-two second-derivative defect after the complex coefficient sum is known to vanish.

Key declarations include:

```text
sourceEntrySecondDerivative_transport
sourceContractRealSecondDerivative_transport_with_defect
sourceContractRealSecondDerivative_transport
sourceAtomRealEnergy_eq_re_im_contracts
sourceAtomRealEnergySecondDerivative_eq_indexAction
```

Thus the former implementation firewall

```text
real contraction identity != complex production source-energy identity
```

is now closed for this exact theorem surface. The warning remains permanent for future arguments: no other real helper may be silently promoted to a complex production theorem.

## FB-03E — production odd jets needed for smoothing

**PROVED / #157**

The exact two-step derivative transport and theorem-backed centered-moment flag close the odd endpoint cancellations required by the #155 generic Riesz theorem.

Validated declarations include:

```text
iteratedDeriv_one_sourceAtomRealEnergy_zero_of_sum_eq_zero
iteratedDeriv_two_sourceAtomRealEnergy_eq_indexAction
iteratedDeriv_add_two_sourceAtomRealEnergy_eq_indexAction
sourceAtomRealEnergy_boundaryFlat_jets_through_six
sourceAtomRealEnergy_even_boundaryFlat_jets_through_eight
```

Therefore:

```text
boundary-flat production carrier
  -> jets 1..6 vanish

even boundary-flat production carrier
  -> jets 1..8 vanish.
```

No pointwise sign of a seventh, ninth or other high derivative away from the endpoint is implied.

## FB-03E — exact production Riesz order 6 / even order 8

**PROVED / #157**

The generic #155 smoothing engine is instantiated without changing that engine.

Validated declarations include:

```text
canonicalPolePrimeDiscrepancyEnergy_eq_rieszSix_of_boundaryFlat
canonicalPolePrimeDiscrepancyEnergy_eq_rieszEight_of_even_boundaryFlat
canonicalSourceChannelEnergy_eq_rieszSix_of_boundaryFlat
canonicalSourceChannelEnergy_eq_rieszEight_of_even_boundaryFlat
```

The complete transformed channel is

```text
canonicalRieszSourceChannelEnergy
```

and retains:

```text
Riesz-transformed pole-prime discrepancy
- reduced canonical archimedean diagonal energy
- reduced canonical archimedean off-diagonal energy
- scalar correction * ||x||^2.
```

No channel has been dropped and no pointwise positivity interpretation is asserted.

## FB-03F — retained transformed-negative first-bad state

**PROVED / #157**

The existing `RegularCellMinimalNegativeEnergyCertificate` is reused rather than replaced by a parallel certificate.

Validated declarations include:

```text
RegularCellMinimalNegativeEnergyCertificate.trial_boundaryFlat
RegularCellMinimalNegativeEnergyCertificate.channelEnergy_eq_rieszSix
RegularCellMinimalNegativeEnergyCertificate.rieszSixNeg
RegularCellMinimalNegativeEnergyCertificate.trial_evenCoefficient
RegularCellMinimalNegativeEnergyCertificate.channelEnergy_eq_rieszEight_of_even
RegularCellMinimalNegativeEnergyCertificate.rieszEightNeg_of_even
```

Consequences:

```text
every retained regular first-bad certificate
  -> complete Riesz-6 source-channel energy < 0

retained first-bad certificate with even parity
  -> complete Riesz-8 source-channel energy < 0.
```

The complete whole-cell ancestry, predecessor nonnegativity, regular zero-shift preimage, negative explicit root and original negative source-channel energy remain attached to the same certificate.

## ExceptionalZero propagation

**PROVED / #157**

Validated declarations include:

```text
exists_regularFirstBad_rieszSixNegativeCertificate_of_offLine_zero
exists_regularFirstBad_rieszSixNegativeCertificate_of_exists_offLine_zero
```

Therefore a hypothetical off-line zero reaches a retained regular first-bad state whose complete order-six Riesz source channel is strictly negative.

This is not a contradiction. It is the transformed negative side of the intended same-state contradiction.

# What changed

Before #157 the project still needed to know whether the #155 generic Riesz engine could legally be instantiated on the actual complex production state and whether the retained first-bad certificate survived that transformation.

After #157 both questions are closed.

The research frontier is no longer analytic legality or transformed-certificate retention. It is now genuinely arithmetic:

```text
Can the exact complete transformed residual on the same forced retained state
be shown nonnegative by an independently justified canonical arithmetic mechanism?
```

FB-03E and FB-03F are consumed theorem dependencies.

# Upstream implications

## Complex-production firewall becomes a closed escape, not a deleted warning

OBS-036 should be reclassified as:

```text
escape closed by #157 for sourceAtomRealEnergy D transport;
permanent warning retained against silent real-to-complex promotion elsewhere.
```

## Odd-jet roadmap obligation is consumed

OBS-035 should likewise record that the missing production odd-jet cancellations through order 6/8 are closed by #157.

The stronger exact leading formulas

```text
g^(7)(0) = -2*(2*pi)^6*|M3|^2
g^(9)(0) =  2*(2*pi)^8*|M4|^2
```

remain **DERIVED / OPEN IN LEAN**. #157 proves the zero cases required for Riesz 6/8, not these coefficient formulas.

# Downstream implications

## FB-04 becomes the live first break

The #152 discovery/certification harness may now be retargeted only to a **specific exact transformed observable/mechanism** aligned with the #157 definition `canonicalRieszSourceChannelEnergy`.

The purpose is not to rediscover that negative transformed states exist; #157 already proves retained Riesz-6 negativity under the hypothetical off-line-zero route.

The purpose is to try to falsify candidate *opposing-sign mechanisms* before Lean investment.

## Candidate arithmetic mechanisms

Current candidates include:

```text
stationarity A x0=b inside the transformed representation
transfer to smaller-size good predecessor energies
whole-cell first-bad minimality across the fixed cutoff cell
exact Riesz boundary-term / first-nonvanishing-jet decomposition
cancellation identities preserving discrepancy + archimedean + scalar structure
combined-parity invariants.
```

Each is **LEAD / HYPOTHESIS** until either falsified or theoremized.

# Resurrected routes

The exact endpoint transport now makes one formerly incomplete idea worth revisiting in a narrower form:

```text
Riesz order r
-> Riesz order r+1
+ explicit right-endpoint boundary term.
```

Because boundary-flatness kills jets through 6 and even boundary-flatness kills jets through 8, the first surviving endpoint term is expected to involve `M3` at the R6->R7 step and `M4` at the even R8->R9 step.

This does **not** resurrect DR-024. It is an integrated boundary decomposition, not a claim that the smoothed integrand has fixed pointwise sign.

# New RH-relevant clues

## First Riesz boundary term

**Status: LEAD / HYPOTHESIS.**

The generic one-step integration-by-parts identity should expose an exact signed boundary contribution when the next endpoint jet is not assumed zero.

Expected schematic form:

```text
E_r = E_(r+1) + B_r
```

where

```text
B_r = (1/L)^(r+1)
      * canonicalPolePrimeRieszPrimitive L (r+1) L
      * iteratedDeriv (r+1) (sourceAtomRealEnergy K x) 0.
```

If the exact seventh/ninth endpoint formulas are later theoremized, the first surviving boundary terms reduce to scalar Riesz-endpoint factors times `|M3|^2` or `|M4|^2` with known transport signs.

This may expose a smaller scalar arithmetic target than the full transformed residual. It must be falsified numerically before being treated as a proof route.

## Complete transformed residual remains the decisive object

**Status: OPEN.**

Any successful nonnegative theorem must apply to the exact same retained state carrying #157's strict negative `canonicalRieszSourceChannelEnergy ... 6` value and must preserve all production channels.

# Falsification checks

1. **Do not revive DR-024.** A boundary-term identity is integrated information, not pointwise sign.
2. **Parity scope:** R6 is universal on retained certificates; R8 is conditional on even retained parity.
3. **Leading-jet scope:** exact seventh/ninth coefficient formulas are not yet theorem authority.
4. **Scaling:** any candidate moment-boundary formula must scale by `|a|^2` under `x -> a*x`.
5. **Prime thresholds:** test proposed scalar Riesz-endpoint signs across prime-power cutoffs and inside fixed cells.
6. **Cancellation:** do not independently coarse-bound pole, prime, arch-diagonal, arch-offdiagonal and scalar terms unless the lost cancellation is quantified.
7. **Circularity:** a proposed nonnegative theorem must not assume successor positivity, absence of the negative root, or `canonicalOneStepDomination` under another name.
8. **Generic countermodels:** mechanisms using only Hermitian/parity/KKT/shell structure remain suspect; exact canonical arithmetic must do work.

# Highest-leverage next moves

1. Synchronize all living docs/control surfaces to theorem authority #157.
2. Theoremize the generic one-step Riesz boundary recurrence without asserting a sign.
3. Theoremize exact seventh/ninth endpoint formulas only if needed by that recurrence.
4. Implement a theorem-aligned numerical/Arb probe for the resulting scalar boundary factors and immediately try to falsify their sign/monotonicity.
5. If the scalar route fails, preserve the counterexample and return to the complete transformed residual using stationarity / lower-size transfer / cancellation.
6. If a scoped mechanism survives falsification, formalize the smallest independently meaningful arithmetic inequality.
7. Compose any proved nonnegative complete transformed-residual theorem with the exact #157 retained negative certificate on the same state.

# Standing questions

**Given everything now formally true, what becomes possible that was not possible before?**

The project can reason directly about a theorem-backed complete transformed negative first-bad state. There is no remaining analytic-legality excuse between the hypothetical off-line zero and the Riesz-transformed negative residual.

**If this contains a clue toward RH, where does it propagate?**

It propagates into FB-04/FB-05: any independent arithmetic nonnegative theorem for the exact same transformed state would immediately produce the missing contradiction.

**What most efficiently tells us whether the clue is real?**

Expose the first nonvanishing Riesz boundary term and try to falsify its scalar arithmetic sign before investing in a large complete-residual proof.

**RH remains OPEN.**
