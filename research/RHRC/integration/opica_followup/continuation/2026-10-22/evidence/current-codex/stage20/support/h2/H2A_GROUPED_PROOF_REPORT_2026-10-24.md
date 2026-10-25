# Exact grouped H2a proof proposal — 2026-10-24

PROVED locally by native Lean: both complete original H2a mathematical statements in the standalone `ConfluentProfilesCandidate.lean` module. Its SHA-256 is `1773e3200a8b3e7284b276d97dcfc5481945e4139852fef8d92e3b64b7b0b0d0`. Both root axiom closures are exactly `[propext, Classical.choice, Quot.sound]`. There is no `sorry`, `admit`, or new `axiom` declaration in this source.

The source was compiled against repository base `6dfabc16220951c9569d75196a237077c532d922`, committed tree `fe4d1757724db0e3588d73d1865b4c579eaf0323`, while Stage20 rate edits were uncommitted. The receipt preserves the working status and exact imported source hashes. This is a source-pinned local proposal, not a claim that the candidate was already committed, installed, cold-rebuilt, or accepted by aggregate CI. The owner must compile the exact installed bytes and run the unchanged source/expected-type/axiom/negative/registry gates before updating original root authority.

RH, Step 4, the 100-root cold receipt and complete release acceptance remain OPEN. The older sealed algebra and right-cell progress archives retain their historical OPEN labels unchanged; this later grouped proof removes their stated canonical-index obstacle.

## Exact mathematical objects

`profileJetMatrix κ m` has rows `0≤n<M`, `M=Σ_j m_j`, and columns ordered `(j,0),…,(j,m_j−1)`. Its entries are precisely

`(1/k!) ∂κ^k [κ(1/4−κ)^n]` evaluated at `κ_j`.

The increasing canonical column index is `Σ_{i<j}m_i+k`, proved bijective to `Fin M`. `profile_jet_confluent_determinant` proves the full original formula

`det = (−1)^(M(M−1)/2) · ∏_j κ_j^(m_j) · ∏_j∏_{i<j}(κ_j−κ_i)^(m_i*m_j)`

for distinct nonzero complex κ nodes. Zero multiplicities are also allowed by the generic proof; the actual-zero theorem uses all actual multiplicity jets.

`distinctSpectralNodes ρ` means injectivity of `j ↦ ρ_j(1−ρ_j)`. `finite_zero_jet_independent` proves complex linear independence of the actual embedded `normalizedZeroMeasureJet ρ_j k`, with index exactly `Σ_j Fin(zeroJetOrder ρ_j)`. Its hypotheses are the actual zeta zero equation, the critical strip, and the distinct-κ reflection quotient. No independent density-zero packet, growth packet, circular independence premise, or invented jet order is supplied. The existing measure type has explicit operations rather than ambient vector-space instances, so independence is expressed in its faithful tempered-distribution embedding, with linear growth proved from the actual domain and multiplicity hypotheses.

The standalone module's only direct project import is the frozen manifest's `Zeta23.OPICAFollowup.CoPoissonJets`. Its other imports are Mathlib. The expected consumer lives in `OPICAConfluentProfilesIndependent`; every `#print axioms` request is fully qualified so the strict output-name parser can remain unchanged.

## Proof and independent validation

The physical proof starts from a zero finite relation among actual embedded measures. The exact lattice subtraction disappears for Schwartz tests supported in the strict first cell `(1,2)`. Mathlib's fundamental lemma yields actual density zero almost everywhere on that interval. A positive-measure subinterval supplies exact right-cell zeros at arbitrarily small positive logarithmic parameters.

The actual first-cell expression is `κ Sh(1/4−κ,u)`. Its normalized κ-jets have finite odd Taylor remainders bounded by

`(‖κ‖+2)^(N+2) expMajorant(‖κ‖+2) |u|^(2N+3)` for `|u|≤1`.

This follows from the existing Cauchy estimate on a unit κ-disc. Only a finite polynomial is differentiated. The remainder constant is independent of the κ-jet order. Coefficient uniqueness along the accumulating positive zero set then gives the exact normalized polynomial Hermite rows. No global physical derivative at `u=0`, mixed-derivative interchange, continuity premise, or transport of null sets through `exp` is used.

Normalized polynomial derivatives are identified with Hasse derivatives. Newton interpolation proves the expanded Hermite determinant. The canonical grouping proof establishes three separate exact identities: occurrence count is the prescribed local `k`; the node product is `∏κ_j^m_j`; and the prior-nonmatching product is the full gap product with powers `m_i*m_j`. These identities preserve the original sign, all factorials, and the true multiplicity restrictions.

The independent expected type writes the full determinant matrix and both products inline, asks for the actual complete-multiplicity family, and checks the precise local `(j,k)` column. Standard-only axiom output is required. The attached negative consumers test removal of distinctness, removal of the affine sign, replacement of normalized columns by raw derivatives, and the false second-parameter-jet coefficient `−1/3` in place of `−1/6`.

There are also formal positive countercontrols: κ=0 gives a zero actual right-cell continuation with a nonzero coefficient; counting an actual zero and its reflection as separate `k=0` columns gives equal actual embedded measures and therefore fails linear independence. The test parameter κ=1/4 used for the factorial check is a kernel test parameter, not an assertion that ρ=1/2 is a zeta zero.

## Post-Green Research Pass

**What changed.** The earlier successful algebra is now connected to the actual physical measures, and the cumulative-order statement is transported to the complete original grouped contract. Canonical grouping is no longer a mathematical or Lean blocker.

**Workflow harvest.** This bundle records local native compiler, expected-type, allowed-axiom and negative-control results only. It ran no new GitHub workflow and grants no cold aggregate authority. Earlier failed assembly logs are preserved solely as diagnostics; their recovery `sorryAx` or spurious failed-declaration output is never accepted. The successful standalone log and exact source hash are the authority for this proposal.

**Upstream implication.** Finite uniform Taylor remainders form a smaller sufficient interface than a full analytic-in-two-variables development. The normalized Cauchy estimate also controls all κ-jet orders with one remainder constant at fixed κ and truncation degree.

**Downstream implication.** The actual H2b finite-span separator can consume a genuine independently established physical basis instead of assuming nontriviality. Realification still needs its explicit Re/Im and conjugation identities: for nonreal conjugate κ pairs the complex coefficients are `(a−ib)/2` and `(a+ib)/2`; for real κ, imaginary jets vanish and should be omitted.

**Resurrected route.** The source paper's complete first-cell/Hermite argument is now a formal composition. The formerly missing normalized confluent determinant and actual coefficient extraction are both resolved locally. The next obstacle is the actual finite real Jordan-span closure and fixed-basis mass estimate, not H2a interpolation.

**DERIVED lead, not a new theorem root.** For `k≥2`, polynomial degree makes all odd coefficients below `n=k−1` vanish; the first nonzero term is `(-1)^(k−1) u^(2k−1)/(2k−1)!`, independent of κ. This gives a first-cell filtration of the higher jets, while also exposing poor conditioning of recovery from very small positive samples.

**RH-relevant falsification.** For nonreal conjugate κ nodes, the exact gap factor includes `(conj κ−κ)^(m²)` and collapses as an off-critical pair approaches the critical line, since `Im κ=(1−2σ)γ`. The limiting conjugate nodes merge into one reflection class. Replacing them by higher κ-jets would require additional actual zero multiplicity; H1 forbids inventing those orders. Thus the determinant supplies no uniform frame constant or automatic positivity limit through such a collision. H2a excludes no individual off-critical zero.

**Highest-leverage next moves.** Install and source-pin the exact module and independently scoped expected consumer; run all unchanged gates. Then compose the actual finite realified span with the original signed sharp-gap separator and prove the fixed-basis weighted negative-mass estimate. Classify the Cauchy, Taylor-uniqueness, Hermite and finite-dimensional norm mechanisms as classical; any originality assessment must concern the source-specific physical construction and its proved restrictions, supported separately by published primary literature.
