# OPICA H2a right-cell continuation progress — 2026-10-24

## Verified status and claim boundary

PROVED by native Lean 4.33.0-rc2: the genuine normalized zero-measure jets are complex-linearly independent when listed in cumulative occurrence order, with every selected order strictly below the actual zero multiplicity. The independent consumer asks for `LinearIndependent ℂ` of the actual `normalizedZeroMeasureJet` objects in their faithful tempered-distribution embedding. All printed axiom closures are `[propext, Classical.choice, Quot.sound]`.

This is supporting research, not completion of either original H2a root. The frozen `profile_jet_confluent_determinant` and `finite_zero_jet_independent` contracts still require the canonical grouped columns `(j,0),…,(j,m_j−1)`, the exact grouped product with powers `m_i*m_j`, the prescribed distinct-κ reflection quotient, production installation, and independent full original consumers. No original ledger root is promoted here. RH, Step 4 and full release remain OPEN.

The checked production Lean source is commit `59ff485551771c0ab6322562d18fb8e9d4166da4`, committed tree `396665de3d14c2db60a4a85c646dd56d718f07ff`. Stage19 documentation and evidence edits were underway during later scratch compiles. The receipt records this and includes status snapshots; that committed tree is not a claim that the working checkout was clean. Imported project source hashes and the sealed algebra dependency hash are recorded in `actual-right-cell-progress-receipt.json`.

## What became formally true

1. `ShFiniteTaylor.lean` proves exact finite Sh-series tail splitting and a uniform remainder bound for `‖w‖≤B`, `|u|≤1`.
2. `ActualJetTaylor.lean` applies the existing actual CoPoissonJets Cauchy estimate on the unit κ-disc. For
   `F_{κ,k}(u)=(1/k!)∂κ^k[κ Sh(1/4−κ,u)]`, its remainder after odd degree `2N+1` is at most
   `(‖κ‖+2)^(N+2) expMajorant(‖κ‖+2) |u|^(2N+3)`.
   The constant is independent of the parameter-jet order `k`. Only a finite polynomial is differentiated.
3. `ExpectedActualJetTaylor.lean` independently states this estimate using the physical expression
   `exp(u/2)*zeroJetDensity κ k (exp u)`, both factorials, and the genuine first-cell domain `0≤u<log 2`.
4. The physical files `ActualMeasureCell`, `ActualMeasureCellAE`, `ActualMeasureCellAccumulation`, and `ActualMeasureRightCell` prove that a zero combination of the actual embedded measures gives first-cell density zero almost everywhere and exact analytic right-cell zeros accumulating at `u=0` from above. The actual lattice subtraction vanishes because tests have support in the strict interval `(1,2)`.
5. The extraction files prove uniqueness of odd coefficients from uniform finite remainders, first on an interval and then on any accumulating positive set. No real-u differentiability premise is supplied.
6. `RightCellIndependence.lean` proves that the exact analytic right-cell continuations are independent for an arbitrary expanded nonzero node sequence with cumulative occurrence orders.
7. `ExpandedActualMeasureIndependence.lean` composes the physical bridge, accumulation extraction, normalized polynomial/Hasse bridge and the sealed determinant algebra. Its hypotheses include actual zeta zeros, the critical strip, and every true multiplicity limit. It derives κ nonvanishing from the strip. `ExpectedExpandedActualMeasureIndependence.lean` independently defines the occurrence count and checks genuine linear independence of actual embedded measures.

The recurrence/order is significant: it counts all earlier equal κ values. It must not replace two reflection-duplicate original blocks by a longer jet chain unless each resulting order is actually available. The original primary theorem requires removing reflection duplicates before forming grouped blocks.

## Exact validation and workflow harvest

`actual-right-cell-progress-receipt.json` contains 11 successful native proof/expected-consumer compilations and one expected wrong-factorial rejection, with source/log hashes and compiler arguments. `actual-measure-cell-receipt.json` and `sh-coefficient-extraction-receipt.json` record the separately compiled physical and extraction support, independent expected consumers, and their negative controls. This campaign ran no new CI workflow. These are local compiler receipts, not cold aggregate or CI release authority. Earlier retained failed logs are diagnostic history only; their `sorryAx` output is never treated as a successful theorem.

The source dependency is the unchanged sealed `OPICA_MATH_SUPPORT_2026-10-24.zip`, SHA-256 `8ad5cc8093ee6219829070c55da8092400c207bfd2a9d7ed43ee4610d2e78533`. It supplies the first-cell identification, Hasse normalization and generic expanded determinant. No compiled object is included in either deliverable archive.

## Post-Green Research Pass

**What changed.** The analytic/physical gap between the successful generic determinant and actual measure independence has been closed in cumulative occurrence order. The proof no longer needs mixed κ/u derivatives, a global density derivative at the lattice boundary, pointwise density continuity, or a change-of-variables theorem transporting null sets through `exp`.

**Upstream implications.** A finite Taylor remainder plus coefficient uniqueness is a smaller interface than a full analytic-in-two-variables theorem. The existing CoPoissonJets Cauchy estimate gives the same remainder constant for every normalized κ-jet order. This can be reused wherever finitely many parameter jets enter a first-cell argument.

**Downstream implications.** Actual finite-span separation can now be connected to a faithful finite linear map once canonical grouping is supplied. This establishes finite nonvacuity for genuine physical objects; it supplies no uniform inverse norm over colliding or growing zero families.

**Resurrected route.** The source paper's first-cell/Hermite route is now supported by an actual measure-to-coefficient proof. The earlier obstacle of justifying interchanged derivatives is eliminated by finite remainders. Canonical finite combinatorics is the remaining H2a implementation bottleneck.

**Creative lead / hypothesis.** The order-independent normalized remainder bound may simplify fixed finite real-span estimates and rigorous local recovery from small positive first-cell samples. This is a lead only. Quantitative inverse conditioning still degenerates under node collisions; the determinant alone does not provide a global frame constant.

**Falsification checks.** The exact second κ-jet cubic coefficient at κ=1/4 is `−1/6`; omitting `1/2!` gives the false value `−1/3`, and the deliberate consumer rejects it. κ=0 gives an actual zero right-cell continuation with a nonzero coefficient, so κ nonvanishing is indispensable. The extraction controls show that same-order errors, or constants depending on the requested small scale, allow a nonzero coefficient. The strict-support control rejects replacing `(1,2)` by `[1,2]`, whose endpoints contain lattice samples. The sealed boundary control proves the global physical test density at κ=1/4 is not differentiable at the lattice boundary; using that two-sided derivative would be wrong.

**Highest-leverage next move.** Prove the three exact canonical grouping identities: occurrence order is the prescribed local `k`; the node product is `∏κ_j^m_j`; and the prior-nonmatching product is `∏_{i<j}(κ_j−κ_i)^(m_i*m_j)`. Preserve the full grouped determinant sign, all multiplicity bounds, and the reflection quotient. Then assemble one production `ConfluentProfiles` module with exactly its frozen direct project import `CoPoissonJets`, compile the original expected consumers and negative controls, and perform the next post-green pass. Only then consider original root promotion.

## Rebuild outline

Use the pinned native Lean toolchain with `LEAN_PATH` containing each package's `.lake/build/lib/lean`, the project `.lake/build/lib/lean`, the extracted sealed algebra directory, and this scratch directory. Compile prerequisites in dependency order. Exact per-file commands are in the receipts. Existing project/Mathlib caches were used; a cold 100-root receipt remains a separate release obligation.
