# Stage 20 — actual jet independence and native window rates

24 October 2026, Europe/Stockholm. Checked code commit **`9a8b2a4baee49f2056c7945b1544a7bc2893735b`**, tree **`6aa53d22d50d2aa24046d73b128c64a1d262f7f3`**. This report records narrow source-pinned theorem evidence; aggregate and full release acceptance remain OPEN.

The original inventory now has **41 historical source-bound roots + 56 additional narrow roots + 3 absent roots**, across the unchanged 100-root / 28-unit contract. Supporting lemmas and independent audit theorems do not increase that count. Mechanical paper-unit evidence coverage is 25 complete / 2 partial / 1 absent; this counts historical or narrow evidence and does not grant formal acceptance of any unit. The three remaining primaries are `finite_zero_span_positive_only_zero`, `fixed_basis_negative_mass_budget`, and `actual_zero_measure_span_consumer`.

## What became formally true

**PROVED, under the exact statements compiled below:**

| Original primary | Exact mathematical content | Independent consumer |
| --- | --- | --- |
| `profile_jet_confluent_determinant` | For distinct nonzero complex κ nodes and arbitrary natural multiplicities, the canonical grouped normalized-derivative matrix has determinant `(-1)^(M(M−1)/2) ∏κ_j^m_j ∏_(i<j)(κ_j−κ_i)^(m_i m_j)`. Empty blocks and the empty matrix are included. | `ExpectedConfluentProfiles` writes every matrix entry and both products literally, and checks the local `(j,k)` column index. |
| `finite_zero_jet_independent` | The actual locally finite complex zero-jet measures are linearly independent as tempered distributions, at actual ζ strip zeros and exactly the available multiplicity jets, provided their κ=ρ(1−ρ) nodes are distinct. Reflected zeros are one node. | The same consumer writes the full physical distribution family, actual zero/strip hypotheses and multiplicity bounds independently. |
| `native_fixed_source_window_rate` | For every original source order d≥0 and every real C>1, the literal continuous `[T−C log T,T]` energy rate `log(1+energy)/(2T)` tends to the actual zero-displacement supremum Θ. Θ=0 and arbitrary multiplicity are retained. | `ExpectedPhysicalRates` unfolds the actual integral and rate normalization. |
| `native_slow_source_window_rate` | The same limit holds along arbitrary real cofinal times and source orders satisfying the original `d_n log(d_n+2)/T_n → 0` condition. A finite nonpositive-time prefix is harmless. | The same consumer retains the exact schedule condition, tests d=0 and `T_n=n−5`, and checks source factors of either logarithmic sign. |
| `fixed_two_factor_mask_rate_theta` | Both actual high-mask realizations, raw and absorbed, of the fixed r=2,d=1,C=2,Q=1,K=8 construction have rate exactly Θ. | `ExpectedArithmeticPhysical` writes the finite-high-pair integrals and actual Dirichlet powers. |
| `quiet_balanced_observation_implies_native_cut` | An explicit cofinal zero-rate upper bound for either complete actual observation implies Θ=0, literal d=0 all-positive-damping L², the native L²/all-damped integral cut, and the existing Step4 conditional conclusion. | The same consumer checks every physical conclusion, including the actual half-line integral and the conditional RH consequence. |

The last theorem has an **OPEN antecedent**. The independent consumer additionally **PROVES** `complete_quiet_upper_iff_zero_supremum`: this quietness condition is exactly as strong as Θ=0 for the complete observations. No independent quietness estimate was supplied. RH, Step4 and the independent closing inequalities remain **OPEN**.

The [clean runner receipt](evidence/current-codex/stage20/runner/CHECK_RESULT.json) establishes PASS_NARROW_ONLY. It builds 24 modules and checks 31 independent consumer files, including the unchanged full word/jet, force/sampling and sample-sign consumers at the new shared `Consumers.lean` source hash. It prints 266 named transitive axiom closures, all contained in `{propext, Classical.choice, Quot.sound}`. The snapshot is clean and unchanged throughout. Lean is 4.33.0-rc2 at `d8b18978322de05a8f3dba51ef03cf5461676c17`; Mathlib remains `51e6992efd06126df61a496bebf8f49482a4e129`. No new project axiom or placeholder is introduced. Build linter/deprecation warnings are retained in the logs.

## Workflow harvest

The complete old-head harvest is preserved in [Stage 19](STAGE19_HANDOVER.md) and its immutable workflow evidence. At `cea7b2f62ea847c18958cc7385151c8c2b09520d`, all 22 runs / 66 jobs completed: 56 success, 6 failure, 4 skipped; 18 successful runs and 4 failed runs. Every job has its actual disposition, previous-result comparison and formal/regression/research classification in that harvest. Those results are authority only for their exact earlier source identity.

The six failures preserve the missing full type review/unauthorized-delta, graph freshness, full-release and component prerequisites. Skips establish nothing. The green scientific wrappers retain their findings: composite-gap falsification; unrestricted shifted-K2 positivity falsification; unresolved canonical realizability; budget-dependent WP4 certificate coverage; a remaining M51 endpoint sliver; finite M71/M45 coverage; M76 pointwise floating ambiguities without inter-grid control; and unchanged bounded native numeric enclosures. None becomes a theorem or closes a research obstruction merely because the new jet and rate theorems compiled.

No exact-new-head GitHub workflow is borrowed from this old harvest. The local clean runner and controls are source-pinned evidence, not a substitute for the required complete final workflow harvest. Current exact-pushed-head dispositions must be reconciled before release acceptance.

The separate W04/W07 and W06 current-source consumers also pass (52 + 14 standard-axiom closures). Record-phase child tests pass 185/185 in each Python mode; real-Linux parent fixtures pass 82/82 in each mode with no skips. Frozen suites replay 5112/18862/14672/1274 checks per mode and three numerical CONSISTENCY_ONLY suites. These infrastructure results confer no additional theorem or release authority.

## What changed

The determinant and independence results close the original H2a analytic bridge, rather than substituting polynomial interpolation for actual measures. The proof passes from actual measure equality to zero compact-test integrals on `(1,2)`, then almost-everywhere density vanishing, arbitrarily small positive exact zeros, normalized κ-jet Taylor coefficients, and finally the grouped confluent determinant. A uniform entire-kernel tail plus Cauchy estimates bounds the actual parameter-jet Taylor remainder. The actual gap-boundary density is generally not differentiable across the gap; the proof correctly uses the analytic right-cell kernel and one-sided positive points.

The window lower bound now combines the actual multiplicity-tail residue, a fixed zero chosen before the horizon, the old-memory bound and continuous-window Cauchy–Schwarz. The old contribution is separated exponentially from the new source contribution. The upper bound controls the actual source envelope, including both signs of the source-factor logarithm. The slow-source theorem discharges these costs under the original schedule condition. It assumes no native-rate conclusion, no attained supremum, no simple-zero restriction and no RH-equivalent upper estimate.

The physical consumers are compositions of these source-specific theorems. The earlier word/jet and force/sampling proof bodies are preserved; their current-source receipts are revalidated. Frozen contracts, original foundational papers, parent mathematical sources, registered historical bindings and protected reviewed graph bytes are unchanged.

## Upstream implications

**DERIVED:** the normalized Hasse-derivative convention is the common algebraic interface beneath the first-cell Taylor matrix and multiplicity-sensitive interpolation. Keeping the canonical grouped enumeration explicit removes ambiguity in signs and cross-block powers. Reflection should be quotiented at κ before selecting a basis; distinct ρ values alone are insufficient.

**DERIVED:** a single schedule theorem subsumes fixed source order, positive-time sequences and finite-prefix corrections. The original MS1 logarithmic cost already dominates the actual `(d+1)/T` cost, including d=0; adding an extra schedule assumption is unnecessary. The continuous energy and its positive-part logarithmic normalization should remain the interface consumed by masks and future observations.

**LEAD / HYPOTHESIS:** the reusable actual entire-kernel tail and normalized Hermite machinery may compress other parameter-derivative arguments. Any such reuse must retain each source’s exact measure and growth requirements.

## Downstream implications

**DERIVED:** once the physical finite-span separation is installed, any nonzero real combination in a specified independent finite basis must have negative off-lattice mass. The H2a result prevents algebraic cancellation of the underlying distinct κ-jet distributions; it does not itself prove that an arbitrary list of their real and imaginary parts is an independent real basis. That separate realification issue must not be hidden in a consumer.

**DERIVED:** an actual off-line zero with displacement δ>0 forces both complete high-mask observations to have exponentially positive growth. For every 0<b<δ, their complete window energies eventually exceed the corresponding positive-rate exponential threshold. A finite quiet prefix cannot establish a cofinal quiet upper bound. This identifies what a future counterexample-exclusion estimate must control; it does not supply that estimate.

**OPEN:** no exclusion of an individual off-line zero follows from H2a independence, positive native rate or the conditional quietness implication. Infinite/nonlinear positive families, boundary collisions and all missing release obligations remain outside these narrow theorems.

## Resurrected routes

The original H2b finite-span/separator route now has its missing full actual H2a prerequisite. Its remaining work is the actual real combination, all signed-measure separator premises and a fixed-basis quantitative negative-mass bound. The earlier generic polynomial proof is superseded by the actual-measure bridge.

The original Q3 physical consumer is now reachable without a caller-supplied native-rate hypothesis. The obstruction moves to proving a cofinal upper estimate for the complete actual observation. The quietness equivalence exposes the full strength of that obstruction; incomplete masks, finite-horizon numerical quietness and synthetic zero observations do not weaken it.

## New RH-relevant clues

**LEAD / HYPOTHESIS:** shrinking the admissible positive counterexample space is the useful next composition: actual finite-jet independence + Fourier self-duality/gap separation + fixed-basis negative-mass budget. This would rule out finite positive linear repairs, with an explicit basis-dependent obstruction. It would still allow infinite-dimensional or nonlinear constructions.

**LEAD / HYPOTHESIS:** conjugate off-critical κ pairs contribute a gap factor `(conj κ−κ)^(m²)` to the determinant. Since `Im κ=(1−2 Re ρ) Im ρ`, that factor collapses as a fixed-ordinate pair approaches the critical line. A quantitative norm estimate must therefore track conditioning and cannot silently use a uniform collision constant. Higher jets at the limiting node would require actual limiting multiplicity, not merely the collision of distinct nodes.

**DERIVED:** for parameter jet order k≥2, the first possible odd right-cell coefficient is independent of κ, at degree `2k−1`; lower degrees vanish. This filtration suggests a structured way to inspect basis conditioning, but it supplies no uniform frame estimate or zero-free region.

## Falsification checks

The [clean control receipt](evidence/current-codex/stage20/controls/CHECK_RESULT.json) records PASS_CONTROLS_ONLY: 15 intended contract mutations rejected and 2 positive actual-kernel degeneracy/normalization sources passed. The mutations cover missing κ distinctness, missing determinant sign, unnormalized jet columns, a wrong `1/2!` coefficient, missing slow-source condition, C=1, missing actual quietness, a synthetic quiet observation, ε=0 damping, and the six preserved force/sampling normalization/domain controls. Rejections are actual compiler type/obligation failures with valid imports, not evidence that every conceivable invalid theorem has been refuted.

Positive Lean controls establish the actual zero-node kernel degeneracy, the κ-jet factorial coefficient and reflection duplication. Exact symbolic checks in the preserved support cover empty/multiple/complex-conjugate/quarter/zero/duplicate-node cases; a single order-three block at κ=2 has normalized determinant −8 versus raw derivative determinant −16, and two simple coalescing nodes give `−ε(1+ε)`. These calculations test normalization and conditioning, not the existence or nonexistence of ζ zeros.

The supporting rate consumers retain Θ=0, d=0, arbitrary multiplicity, nonpositive finite time prefixes and source factors with either logarithmic sign. A proved synthetic finite-prefix counterexample shows why finite numerical quietness does not imply the required cofinal estimate. The complete-observation quietness equivalence explicitly tests the route for circular strength.

The C=1 rejection checks the original interface; it does not prove a stronger C=1 theorem false. Likewise, failure to discharge MS1 after omitting its schedule hypothesis is not a counterexample to every faster schedule. A boundary schedule of order `T/log T` can have a nonvanishing `d log(d+2)/T` cost and needs a separate analysis.

## Novelty assessment against the 17-paper baseline

The preserved [Drive/corpus audit](evidence/current-codex/stage19/novelty/OPICA_NOVELTY_AND_DRIVE_AUDIT_2026-10-24.md) reconstructs 16 of 17 manuscript bodies and identifies the missing Moment–Jet manuscript by citations; it does not claim a complete body-level comparison. The historical cutoff is PR #284 at `5e7253bffa570c0e07052b8d59a0949cdbcabdbe`. Root IDs and supporting lemma counts are not counts of discoveries.

**Classical mechanisms:** normalized confluent Vandermonde/Hermite interpolation and separation-dependent inverse conditioning are classical; see Gautschi’s [1962 primary paper](https://www.cs.purdue.edu/homes/wxg/selected_works/section_01/016.pdf). Multiplicity-sensitive zero evaluators and finite evaluator independence already occur in Burnol’s published [2004 paper](https://www.numdam.org/articles/10.5802/jtnb.434/), especially Theorems 3.1–3.3 and the discussion following Lemma 7.4. Co-Poisson/ζ-transform constructions also have substantial prior art in Burnol’s [2007 paper](https://www.numdam.org/item/AIF_2007__57_2_525_0/). Generic determinant, interpolation, finite-system independence and compactness arguments receive no priority claim here.

**Source-specific constructions:** the exact actual locally finite normalized ζ-jet measure realization, κ reflection quotient, physical right-cell analytic bridge, original-source continuous rate theorem, original MS1 source schedule and exact fixed-mask compositions are now formal constructions in this repository. Their equivalence or distinction from the published prior objects is not proved. They are originality candidates requiring a precise comparison, not established worldwide novelties.

**Incomplete claims:** independent quietness, a uniform collision/growing-basis budget, infinite/nonlinear positive-family exclusion, RH and Step4 remain OPEN. No global originality or priority claim is established. The sample-sign consequence was already present in the frozen paper and remains supporting mathematics.

## Highest-leverage next moves

1. Finish the three original actual finite-span roots, using genuine measure construction and an explicitly independent fixed real basis with the Euclidean coefficient norm. Attack self-duality, weighting and degenerate-basis assumptions with controls.
2. Inspect the resulting obstruction quantitatively: identify the exact mechanism by which negative-mass constants degenerate under κ collisions or growing bases. Distinguish a useful necessary condition on an infinite limit from an unjustified uniform estimate.
3. Assemble the full100 exact-type facade and fresh cold compiler closure; keep independent type review and release acceptance separate from diagnostic compilation. Reconcile actual parent extension, registry/dependency maps, canonical outputs and every final exact-head workflow without self-invented approval.
4. Compare the actual jet-measure realization with Burnol’s evaluator objects at the level of an explicit transform or pairing. This has higher novelty information gain than assigning priority from theorem counts.

The standing mathematical question remains: given what is now formally true, which additional actual constraint would rule out an admissible off-critical-zero construction, and which fastest falsification would test that constraint?

Still OPEN: the three original finite-span primaries; aggregate 100-root exact-source/type acceptance; the independent full review; full parent/registry/dependency/canonical/runtime/workflow acceptance; independent complete-observation quietness; RH; Step4; and the independent closing inequalities.
