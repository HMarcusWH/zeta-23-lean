# OPICA — Exact repository build specification

**Specification date:** 21 October 2026  
**Repository:** `HMarcusWH/zeta-23-lean`  
**Proposed branch:** `research/opica-obstruction-preservation`  
**Proposed PR title:** *Formalize OPICA preservation architecture and native source adapters*  
**Status:** specification only; no branch, PR, theorem, registry promotion or workflow run created by this specification.  
**Claim status:** RH / Step 4 / A-X / B-Y / C-Schur / OPEN-J46 remain OPEN.

## 0. Build decision and exact footprint

Build one additive OPICA theorem package, with a separate public import, exact source-bound native consumers, its own compiler receipt, and integration into the existing registered-theorem and derived-state machinery. Do not rewrite the historical Step 1–3 producer or try to make its acceptance contract stand for OPICA.

| Kind of change | Required footprint |
|---|---:|
| New Lean files | 26: 23 mathematical modules including the facade, 3 audit modules |
| New integration/document/control files | 23 |
| New workflow | 1 |
| **New tracked files, total** | **50** |
| **Existing authoritative files edited** | **9** |
| Existing producer-controlled files rematerialized | 62; only the byte-changed subset enters the diff |
| Deletions / renames | 0 |
| Primary semantic theorem roots | 76 proposed roots covering all 25 paper statement families plus 7 native adapters |

These counts specify a full-paper PR, not a claim that its proofs have already been implemented. The original nine broad module headings are refined into smaller proof/foundation files without weakening their mathematical scope. A heavy theorem cannot be replaced by an assumed version of itself or an abstract certificate carrying its conclusion.

If a required formalization remains incomplete, this full-paper PR remains incomplete. A smaller core-only PR would require an explicit rescoping and a different coverage claim; it is not the silent fallback of this specification.

### 0.1 The checked base

- Main commit: `97926d6a949fed7af0429a373b47abc772012834`.
- Base tree: `3b8fb2b29f53247ad5143a603c047e160bddd37c`.
- Lean: `leanprover/lean4:v4.33.0-rc2`.
- Mathlib: `51e6992efd06126df61a496bebf8f49482a4e129`.
- `lakefile.toml`: default target is `Zeta23`; the existing `lean_lib Zeta23` is retained.
- Live open-PR collection was empty when read. No future PR number is reserved or inferred.

Live main and selected immutable source blobs were read through the GitHub connector. The entire 2,330-file local snapshot was rechecked against the inherited full content inventory. This is **not** a fresh full-tree GitHub download, a new Lean build or a new CI harvest. The provenance receipt distinguishes fresh reads from the inherited immutable tree association.

Before implementation, fetch main again. If it differs, reconcile every file precondition and rerun the specification validator. Do not silently apply the old source hashes to a different tree.

### 0.2 Inputs and non-goals

Freeze the exact OPICA paper Markdown, implementation contract and theorem/audit ledger under the new integration folder. Their original PAPER status is retained. Formal authority lives in separate compiler receipts and reviewed registry rows, never by editing the historical ledger's `implemented_this_turn` fields.

Not part of this PR: proving the native full-window theorem J5.2 or MS1, constructing a native contact-to-heat defect, establishing an RH-closing upper, completing D2, importing the external 7/8 theorem, changing the toolchain, or weakening old review and claim gates. Generic theorems whose hypotheses mention an energy limit remain generic implications until a separate native proof supplies that limit.

## 1. Files to create

All paths below are exact proposed paths, checked absent at the pinned base. Private helper declarations may be added inside these files. Adding a new tracked file or moving a public theorem between files requires an explicit manifest/DAG/crosswalk revision before acceptance.

### 1.1 Mathematical and audit Lean files

| Path | Role / required result | Build wave |
|---|---|---|

| `Zeta23/OPICA/LocalData.lean` | Source-tagged simple-pole witnesses, exact multiplier-order data, punctured/genuine-neighborhood identities and normalized Taylor observations. | 1 |

| `Zeta23/OPICA/LocalObstruction.lean` | Unit-residue and finite-order completion laws; lower-jet vanishing; residual congruence; repeated completion and factorial/binomial normalization. | 1 |

| `Zeta23/OPICA/LocalQuotients.lean` | Holomorphic-germ/Taylor quotient construction; zero ideal equality; pole-carrier to leading-jet isomorphism. Full L2 quotient clauses, not merely its residual corollary. | 2 |

| `Zeta23/OPICA/ResidueLimits.lean` | Contour-norm residue continuity on a common disk and the escaping-tail counterexample with separate convergence/continuation domains. | 2 |

| `Zeta23/OPICA/AffineTransport.lean` | Finite affine recursion, correction ledger, product/order propagation; raw cancellation control. | 1 |

| `Zeta23/OPICA/EnergyRate.lean` | Positive horizon schedules; real/complex log comparison; subexponential additive error, positive-part/magnitude rates, extended limsup/liminf, two-sided scale costs. | 1 |

| `Zeta23/OPICA/Composition.lean` | Accumulated affine budget, cofinal consumer, quotient faithfulness and source-typed finite paths. Native rate hypotheses stay explicit. | 1 |

| `Zeta23/OPICA/ObservationCompatibility.lean` | Kernel recovery criterion, finite-dimensional range/left-annihilator equivalence and exact distance formula; equivalent observations preserve solution sets. | 1 |

| `Zeta23/OPICA/DivisorBounds.lean` | Ordered factorization counts with positive indices; submultiplicativity, array-surjection square bound, explicit harmonic and square-root sums. | 2 |

| `Zeta23/OPICA/PrimitiveMasks.lean` | Actual finite-at-horizon translate sums, positive integer indices, gcd-reduced low/high masks, measurable cutoff and integrability interfaces. | 2 |

| `Zeta23/OPICA/DivisorMask.lean` | Full low-primitive integral bound, both masked Type I estimates, balanced comparison and two-mask regrouping/rate consumer. | 2 |

| `Zeta23/OPICA/WeightedLaplace.lean` | Weighted causal L2 holomorphy, all derivative estimates and source-identified continuation/pole incompatibility. Strict half-plane only. | 2 |

| `Zeta23/OPICA/RangeSeparation.lean` | Continuous annihilator and positive distance from actual range closure; functional norm and zero cases treated explicitly. | 1 |

| `Zeta23/OPICA/NativeJetAdapter.lean` | Bind OPICA to existing physical input/kernel jets, selected right zero, damping, multiplicity and a single GeneratedStep123CompleteOutput. No native nonzero-jet premise. | 3 |

| `Zeta23/OPICA/NativeArithmeticAdapter.lean` | Construct the original j-drive bounded-causal instance, finite palette compensation and the actual low-mask instance. No higher-source/J5.2/MS1 premise promoted. | 3 |

| `Zeta23/OPICA/Involution.lean` | H3 linear-involution commutator theorem and zero selfdual projection on the common admissible domain. | 1 |

| `Zeta23/OPICA/LocallyFiniteSignedMeasure.lean` | Locally finite real signed-measure representation with linear total-variation growth and faithful embedding into tempered distributions. No finite-global-variation shortcut. | 4 |

| `Zeta23/OPICA/SincTriangle.lean` | Exact sinc-squared/triangle Fourier pair; Gaussian regularization, legitimate signed pairings and lattice Poisson summation needed by H1/H4. | 4 |

| `Zeta23/OPICA/SignedHeatSeparator.lean` | Full signed sharp-gap rigidity and global negative off-lattice mass bound; integer support, periodicity and origin atom. | 4 |

| `Zeta23/OPICA/FejerCompletion.lean` | Convergent Fejer lattice sum, floor formula, exact affine native-completion transform and one-sided cusp derivatives, with analytic domains. | 4 |

| `Zeta23/OPICA/FourierCompatibility.lean` | Stable public import surface for H1-H4; no assumed native contact-to-defect construction. | 4 |

| `Zeta23/OPICA/Counterexamples.lean` | Kernel-checked exact controls for affine cancellation, inverse scale loss, accumulated cost, wrong masks, rank-one/PSD inferences, projection loss and overdetermination. | 3 |

| `Zeta23/OPICA.lean` | Normal mathematical public facade. Imported directly as Zeta23.OPICA; not an audit executable and not added to legacy headline root. | 4 |

| `Zeta23/OPICA/Validation.lean` | Explicit typed consumers covering every required statement clause and the actual same-state native adapters; #check/#print-axiom surface is audit-only, not in the normal facade. | 5 |

| `Zeta23/RHRC/OpicaTypeExprExport.lean` | Audit-only, source-attributed copy/adaptation of the frozen private Expr DAG serializer. Public exportType helper; fail-closed size limits; no mathematical authority. | 5 |

| `Zeta23/RHRC/OpicaBindings.lean` | Compiler environment enumeration; exact module/kind resolution, full type/constructor DAGs, root axiom footprints and TYPE/VALUE/STRUCTURE dependencies. | 5 |

**Public import:** `import Zeta23.OPICA`.

The facade imports mathematical modules only. It must not import `Validation`, `OpicaBindings`, the type serializer, or any other RHRC audit module. `Validation` imports the facade; the audit bindings import `Validation`. This one-way relationship prevents compiler instrumentation from becoming a mathematical dependency.

`LocalQuotients`, `ResidueLimits`, `DivisorBounds`, `PrimitiveMasks`, `WeightedLaplace`, `RangeSeparation`, `LocallyFiniteSignedMeasure`, `SincTriangle`, `SignedHeatSeparator`, `FejerCompletion`, `Involution` and the second native adapter are implementation refinements of the paper's broad module list. They keep difficult mathematical foundations visible rather than burying them in one file or postulating them.

### 1.2 Integration, tests and documentation

| Exact new path | Purpose |
|---|---|

| `research/RHRC/integration/opica/README.md` | Public scope, import/build commands, proof/experiment distinction, pointer to exact paper and specifications. |

| `research/RHRC/integration/opica/BUILD_SPEC.md` | Approved build specification and scope: this document copied with its source identity. |

| `research/RHRC/integration/opica/BUILD_MANIFEST.json` | Allowed source delta, package import DAG, whole-paper coverage and pinned preconditions. |

| `research/RHRC/integration/opica/PUBLIC_ROOTS.json` | Required semantic theorem roots, kinds, modules, paper IDs, signatures and full public-namespace inventory policy. |

| `research/RHRC/integration/opica/PAPER_CROSSWALK.json` | Every clause of all 25 paper statements and 38 corrections mapped to root(s), controls, native/external status. |

| `research/RHRC/integration/opica/SOURCE_REGISTER.json` | Immutable paper-input hashes, repo/Lean/Mathlib pins, source-attributed codec, inherited-vs-new evidence scope. |

| `research/RHRC/integration/opica/PROTECTED_STATE.json` | Baseline bytes and JSON object projections forbidden to change; historical claims and D2/review state. |

| `research/RHRC/integration/opica/WORKFLOW_CONTRACT.json` | Required OPICA jobs and complete inherited-workflow harvest policy with explicit skips and attempts. |

| `research/RHRC/integration/opica/POST_GREEN_RESEARCH.md` | Actual post-green proof/CI/discovery harvest to be completed when results exist, initially explicitly pending; never auto-approve mathematical review. |

| `research/RHRC/integration/opica/validate_contract.py` | Fail-closed static file/namespace/25-ID coverage/import/firewall/classifier validation; outputs to supplied external artifact directory. |

| `research/RHRC/integration/opica/build_receipt.py` | Read exact compiler logs, validate lossless type DAGs/constructor types/axioms/source binding, emit receipt outside tracked tree. |

| `research/RHRC/integration/opica/harvest_workflows.py` | Consume paginated GitHub check/job/run records, preserve attempts, resolve exact effective jobs and reject unresolved required evidence. |

| `research/RHRC/integration/opica/dependency_delta.py` | Compare compiler-derived uses and theorem/paper coverage with baseline; emit structural research delta, no logical-equivalence promotion. |

| `research/RHRC/integration/opica/check_exact.py` | Reproduce the paper 5,112 finite controls using checks that remain active under Python -O; distinguish any additional controls. |

| `research/RHRC/integration/opica/tests/test_contract.py` | Missing/wrong path, duplicate root, missing subclause, import-cycle and no-placeholder/forbidden-scope mutations. |

| `research/RHRC/integration/opica/tests/test_receipt.py` | Stale head/tree, wrong module/kind/source, missing/duplicate root, truncated DAG, hidden typeclass premise, extra axiom and semantic nonclaim mutations. |

| `research/RHRC/integration/opica/tests/test_workflow_harvest.py` | Running/skipped/cancelled required jobs, partial reruns, stale synthetic merge, foreign head/tree, duplicate and conflicted run identities. |

| `research/RHRC/integration/opica/tests/test_file_classes.py` | All new paths classified; Validation/audit helpers AUDIT_ONLY; native adapters RH_FORMAL_CORE; historical fixtures stay fixtures. |

| `research/RHRC/integration/opica/tests/test_no_scope_promotion.py` | Four original OPEN records, old 118 theorem rows, STEP4_CUTS, original proof bytes, D2 and review gates remain unchanged. |

| `research/RHRC/integration/opica/tests/test_dependency_delta.py` | Dependency provenance and count/report drift; structural sharing must not be reported as mathematical equivalence or closure. |

| `research/RHRC/integration/opica/paper/OPICA_Paper_Construction_v1_0_2026-10-21.md` | Exact paper source bytes; no silent corrections. |

| `research/RHRC/integration/opica/paper/OPICA_Lean_Implementation_Contract_2026-10-21.md` | Exact source contract, with refinements explained only in BUILD_SPEC/PAPER_CROSSWALK. |

| `research/RHRC/integration/opica/paper/OPICA_Theorem_and_Audit_Ledger_2026-10-21.json` | Exact paper ledger, including paper-only dependencies and OPEN targets; formal status belongs to separate new receipts. |

### 1.3 Dedicated workflow

Create **`.github/workflows/rhrc_opica.yml`**. No existing workflow is changed. It explicitly builds the new public facade and all validation/exporter entrypoints, runs the finite regression and contract mutations, emits the structural dependency delta, and fails closed if any required component is unfinished.

No PDF, evidence ZIP, existing repository snapshot, tool cache or final-head compiler receipt is committed to this new integration folder. Paper source and source hashes are sufficient; large binary and execution outputs are workflow artifacts / Drive releases.

## 2. Existing files to change

These are the only nine hand-edited existing files. The machine manifest includes their exact base Git-blob SHA, SHA-256 and byte length. Existing mathematical proof files are dependencies, not edit targets.

| Existing path | Exact intended change |
|---|---|

| `Zeta23/RHRC/RegisteredClaimBindings.lean` | Append direct imports for new registered theorem defining modules and exact #check/#print axioms lines. Existing rows unchanged; no import of Validation or OpicaBindings. Import list must equal registry-derived module set. |

| `research/RHRC/CLAIM_REGISTRY.json` | Append source-bound OPICA_* theorem claims only after those exact roots compile and pass semantic/axiom review. Generic claims state all premises. All existing 122 records unchanged. No new route assigned; no closing predicate promoted. |

| `research/RHRC/REGISTERED_THEOREM_BINDINGS.json` | Append one binding per approved OPICA primary theorem root; source and module must match compiler. Preserve all old 118 bindings, candidate fields, schema and RH_OPEN. |

| `research/RHRC/graph/FILE_CLASSES.json` | Insert narrow rules ahead of generic Zeta23 rule: OPICA Validation is AUDIT_ONLY; NativeJetAdapter and NativeArithmeticAdapter are RH_FORMAL_CORE; other OPICA modules are AUXILIARY_FORMALIZATION. Existing classifications unchanged. |

| `research/RHRC/graph/SEMANTIC_CLOSURE_CONFIG.json` | Add exact standalone-module roles for the 26 new Lean modules (mathematical API, native adapters, validation and audit exporters), preserving every old role. Root Zeta23.lean is unchanged, so old reachability must stay unchanged. |

| `research/RHRC/tools/run_suite.py` | Add dependency-light OPICA static contract check and unittest discovery. Preserve every existing check and --skip-derived-state meaning; do not silently invoke a generator or expensive independent research campaign. |

| `README.md` | Add dated OPICA section with explicit import, dedicated build/CI, scope and OPEN firewall; do not rewrite historical authority sections or upstream headline theorems. |

| `research/RHRC/README.md` | Add OPICA package navigation and exact formalization/CI status with link to crosswalk and receipt artifact; preserve legacy route statuses. |

| `research/RHRC/CURRENT_RESEARCH_PLAN.md` | Add OPICA implementation checkpoint and post-green questions; retain all unresolved arithmetic/contact/native-rate targets and D2 disposition. |

### 2.1 Why the three registry files move together

At the base there are **122 claims, 118 proved theorem bindings and four OPEN claims**. The existing registered-theorem linter requires the proved registry, binding manifest, defining-module imports, `#check` lines and `#print axioms` lines to agree exactly.

After each required semantic root has an actual proof, exact type review and allowed-axiom receipt, append its `OPICA_*` claim and exact binding. Do not insert unimplemented roots into the global registry as new OPEN claims: that would violate its intentionally fixed OPEN set. Planned status belongs in OPICA's own manifests while proof work is incomplete.

With all 76 specified roots accepted, the expected totals are **198 claims and 194 proved bindings**, with these original four OPEN entries unchanged:

```text
C_RH
R001_PRIME_UPPER
R002_WINDOWED_VISIBILITY
R003_COFINAL_CANONICAL_ARITHMETIC_CERTIFICATES
```

New claims are route-less supporting mathematical claims. `ROUTE_REGISTRY.json` does not change. Their statement text must describe the exact implication, including analytic, source, domain and rate hypotheses. A proved generic implication is not a proved native premise. Use the existing registry's `PROVED_UNCONDITIONAL` label only for the proved statement as quantified; never use it to assert an antecedent not proved by that declaration.

Keep the old 122 claim objects and 118 binding objects identical. New registry dependencies must reflect any mapped registered roots actually used; compiler TYPE/VALUE/STRUCTURE evidence remains authoritative and is not replaced by a hand-edited dependency list. No new dependency is added to the old RH-closing claim.

### 2.2 Trust classifications and graph reachability

Insert the following narrow rules before the generic `zeta_lean` rule:

```text
^Zeta23/OPICA/Validation\.lean$
    LEAN_SOURCE / AUDIT_ONLY
^Zeta23/OPICA/(?:NativeJetAdapter|NativeArithmeticAdapter)\.lean$
    LEAN_SOURCE / RH_FORMAL_CORE
^Zeta23/OPICA(?:/.*)?\.lean$
    LEAN_SOURCE / AUXILIARY_FORMALIZATION
```

The existing `Zeta23/RHRC/.*` rule already makes both new exporters AUDIT_ONLY. Existing integration-file and workflow rules classify the other new files. All historical file classifications must remain unchanged.

The semantic closure checker requires an **exact set** of standalone-module dispositions. Add all 26 new modules, using `OPICA_GENERIC_FORMALIZATION`, `OPICA_SOURCE_BOUND_NATIVE_ADAPTER` or `OPICA_AUDIT_ONLY` as appropriate. The proposed exact role map is included in `OPICA_PR_INTEGRATION_PATCH_SPEC_2026-10-21.json`.

The old root import closures remain unchanged. The new modules are intentionally standalone with respect to the legacy root, but not orphaned: they are compiled explicitly, imported by the new facade, consumed by typed validation and linked from registered theorem bindings. Graph reachability is descriptive, not a substitute for compiler authority.

### 2.3 Explicit non-edits

Do not edit `Zeta23.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `formalization.yaml`, the comparator, any existing `Zeta23/CCM/**` or `Zeta23/ExceptionalZero/**` proof, or the historical Step123 output structures.

Do not edit existing workflow files, the historical `integration/post290/**` contracts/receipts/review scripts, D2 datasets, `BOUNDARY.json`, `R003_PROMOTED_BINDINGS.json`, `ROUTE_REGISTRY.json`, or frozen generated history. The old A-X/B-Y/C-Schur sufficiency file is a protected reference, not the place to attach OPICA by adding new unproved hypotheses.

The only existing Lean file edited is the registered-claim **audit** surface. Its import additions must be the exact new defining modules required by the binding linter, not arbitrary aggregate imports.

## 3. How the mathematics is wired

### 3.1 Import direction

An arrow below means “is imported by / supplies facts to,” not “proves the next layer's premises.”

```text
LocalData -> LocalObstruction -> LocalQuotients
                      |-------> AffineTransport --+
EnergyRate ---------------------------------------+-> Composition
LocalData -> ResidueLimits

DivisorBounds ---+
PrimitiveMasks --+-> DivisorMask <- EnergyRate

ObservationCompatibility
RangeSeparation
LocalData -> WeightedLaplace

existing actual input/kernel jets + Step123CompleteOutput
  + LocalObstruction + Composition + RangeSeparation
  -> NativeJetAdapter

existing original-j drive/source + DivisorMask
  -> NativeArithmeticAdapter

LocallyFiniteSignedMeasure -> SincTriangle -> SignedHeatSeparator
                                     |----> FejerCompletion <- existing native floor completion
Involution + SignedHeatSeparator + FejerCompletion
  -> FourierCompatibility

mathematical modules + native adapters + Counterexamples
  -> Zeta23.OPICA
  -> Validation
  -> RHRC.OpicaBindings <- RHRC.OpicaTypeExprExport
```

The exact direct project-import DAG, including existing module names, is machine-readable in the build manifest and in the `.dot` file. Mathlib imports must be checked at the pinned revision during implementation; current online API names are not a promise of pin-compatible elaboration.

### 3.2 The local analytic carrier

`LocalData` defines a visible simple-pole witness with center, nonzero residue, analytic remainder and equality on a **punctured** neighborhood. Multiplier data records a nonnegative integer order and a nonvanishing analytic factor with genuine-neighborhood equality.

For positive order `k`, use the explicit analytic representative

\[
(z-\lambda)^{k-1}u(z)\bigl[R+(z-\lambda)h(z)\bigr].
\]

The public theorem proves analyticity, lower-derivative vanishing, exact order and the leading derivative with its factorial. It does not evaluate the totalized division expression at the singular point. Include `k=0`, multiplicity one and higher multiplicities, powers and the double-completion binomial factor.

`LocalQuotients` must prove the actual holomorphic-germ/Taylor quotient correspondence. Witness-based local lemmas can be implemented first, but their successful build does not cover the paper's quotient-isomorphism subclause by itself.

`AffineTransport` retains every correction. Its raw-cancellation control is part of the accepted theorem surface. `ResidueLimits` states the common disk, pole restriction and uniform contour topology; compact-time convergence alone never supplies residue convergence.

### 3.3 Rate and composition interfaces

`EnergyRate` defines the schedule and subexponential predicates by their actual limits, not as opaque properties of the prime field. Positivity of horizons, horizon divergence, magnitude versus positive-part observations and inverse scaling cost are explicit. Extended limsup/liminf clauses cannot be silently omitted because a finite-limit corollary is easier.

`Composition` contains the precise accumulated product and suffix-product error sum. Its finite-path interface carries state admissibility, observation maps and actual commuting equations/zero reflection. A field whose type says “this bridge works” is allowed only as an explicit generic premise, never as a fabricated native witness.

The quiet-cofinal theorem consumes a supplied full-rate limit. It does not produce quiet windows or formalize native J5.2/MS1. Keep its theorem name and registry wording generic.

### 3.4 Observation and independent-constraint interfaces

`ObservationCompatibility` proves kernel factorization, finite-dimensional left-annihilator incompatibility and distance duality. It uses complex conjugate adjoints correctly. The zero-residual and zero-dimensional cases are included. Equivalent data transformations preserve existing solution sets; more sampled rows alone do not give inconsistency.

The counterexamples use actual matrices, projections, finite products or elementary functions. An identity about a supplied matrix is not represented as a theorem identifying a native Gram matrix with that matrix unless the identification is separately proved.

### 3.5 Arithmetic mask interfaces

`PrimitiveMasks` uses positive integer indices, the exact cutoff `max(d,e)/gcd(d,e)`, diagonal inclusion on the low side, and strict complementary high side. The cutoff is measurable on the observation interval; the drive is measurable, bounded and causal with a nonnegative gap. Prove that on a fixed horizon the true translate sums reduce to a single finite index bound before exchanging sums and integrals.

`DivisorBounds` proves the ordered-factorization inequalities and explicit weighted sums, including the row/column-array surjection. No new abstract asymptotic divisor bound is a substitute.

`DivisorMask` proves the complete integral estimate, both mixed Type I terms, the combined balanced comparison and the separately priced regrouped-mask identity. A theorem taking “the low-mask bound” as an input proves only a corollary, not A2. Repeated primes and common-gcd/primitive overlap are retained.

`NativeArithmeticAdapter` supplies at least one concrete original-\(j\) consumer using the existing `nativeOriginalIntegerDrive`, its continuity, support and rapid fixed-order bounds. It constructs the bounded-causal witness and finite-palette compensation; it must not take those facts as unexplained caller hypotheses. It does **not** invent the moving high-source family, J5.2/MS1, or the missing complete signed upper.

### 3.6 Fourier/measure interfaces

H1 is about **locally finite** signed measures, not necessarily finite total variation on the whole real line. Do not substitute Mathlib's globally finite signed-measure carrier and silently narrow the paper theorem.

A concrete implementation may use a mutually singular pair of positive locally finite measures with linear growth for their sum, together with a proved faithful embedding of their difference into tempered distributions. Define equality and restriction through the measure pair/compact tests consistently; avoid undefined `infinity - infinity`. This representation choice must be proved equivalent to the stated class, not assumed to have the rigidity conclusion.

`SincTriangle` proves the Fourier pair and justified regularized pairings. `SignedHeatSeparator` then derives lattice support, distributional periodicity and zero mass. `FejerCompletion` derives the exact native floor formula, actual convergent lattice sum, Laplace identity with rational correction and the two one-sided derivatives. Importing a numerical rational check, assuming Poisson at the needed nonsmooth class, or assuming the final pairing identity is not full H1/H4 coverage.

`Involution` is a genuinely independent algebraic first submodule. H3 can compile before H1, but H1/H2 do not become proved because H3 is green. No native contact-to-measure construction is supplied by these generic theorems.

## 4. Binding to the existing native proof state

### 4.1 Native jet adapter: exact inputs and outputs

The defining native source modules are unchanged. Reuse these established identifiers, in their actual namespaces:

```text
Zeta23.ExceptionalZero.nativeZeroMultiplicity_order
Zeta23.ExceptionalZero.nativeZeroMultiplicity_deriv_order
Zeta23.ExceptionalZero.nativeZeroJetKernelMultiplier_order
Zeta23.ExceptionalZero.nativeZeroJetInputMultiplier_order
Zeta23.ExceptionalZero.nativeZeroJetInputMultiplier_jet
Zeta23.ExceptionalZero.nativeZeroJetSourceFactor_ne_zero
Zeta23.ExceptionalZero.nativeActualInputLaplace_eventuallyEq_multiplier
Zeta23.ExceptionalZero.nativeActualInputLaplace_order_of_zero
Zeta23.ExceptionalZero.nativeCompletedInput_zeroJet_value
Zeta23.ExceptionalZero.nativeCompletedInput_zeroJet_ne_zero
```

The source's right-zero selection, `nativeZeroJetDamping`, `nativeZeroJetParameter`, multiplicity preservation and genuine-neighborhood transform equality must be transported exactly. The physical pairing has phase \((-1)^m\); the raw completed derivative has the corresponding derivative formula. Do not insert an extra factorial or confuse the two observations.

Define a downstream OPICA view of an existing `GeneratedStep123CompleteOutput`/range obstruction, then prove that its source/field observations agree. Do not add fields to the historical structure, and do not construct a second unrelated packet to satisfy each output. The phase-cofinal consumer must preserve **each phase separately** and its requested lateness; it must not claim two good phases at one aperture.

The range-distance theorem can combine the generic annihilator theorem with the actual physical nonzero pairing. Its default native instance uses the already selected damping. A broader arbitrary-damping statement must be separately proved if desired; it is not inferred from the paper note's generality.

### 4.2 How the generic calculus is genuinely consumed

A native wrapper that merely restates the old nonzero-jet theorem is useful provenance but does not test the new calculus. The typed validation therefore includes:

1. an actual-input witness built from the existing physical transform equality and analytic-order facts;
2. a residual multiplier `1 + Z*b` acting on a visible local pole witness, with source identity kept separate;
3. a completion/affine transport consumer that uses L1/L4 and the old source factors at the correct center;
4. the generic range-separation bound instantiated with the old native annihilator and input;
5. an original-drive low-mask instance using A2 and the real source;
6. finite projection and compatibility examples testing loss of observation;
7. a conditional energy comparison whose full-rate premise is visible in its final type.

These consumers make the generic-to-native wiring explicit without upgrading the unformalized native energy/contact inputs. The formal statement and its proof term, not a declaration name, determine which new lemma is actually used. The dependency-delta job must report that use truthfully.

## 5. Exact statement and root coverage

The primary-root file lists **76 proposed theorem names**. Every paper family is mandatory, and all definitions/structures/constructors plus additional public theorem helpers are compiler-enumerated beyond that primary list. The 25 paper labels are not a license to certify one trivial corollary per label.

The full names below use namespace `Zeta23.OPICA`. They are proposed interfaces, not existing declarations or checked Lean signatures. `Validation.lean` must supply an expected type expression for every root after the named data types are defined; the compiler then checks exact definitional equality, and the receipt records the elaborated full type. Until that happens, no type digest or proof-success field is invented.

### L1 — General local multiplier law

- `Zeta23.OPICA.unit_mul_simplePole_residue` — `Zeta23.OPICA.LocalObstruction`.
- `Zeta23.OPICA.completion_regularRepresentative_analytic` — `Zeta23.OPICA.LocalObstruction`.
- `Zeta23.OPICA.completion_order` — `Zeta23.OPICA.LocalObstruction`.
- `Zeta23.OPICA.completion_leading_jet` — `Zeta23.OPICA.LocalObstruction`.

Required content: Exact finite multiplier order, analytic representative and normalized leading derivative; lower derivatives vanish; center equality never inferred from punctured totalized division.

### L2 — Zero ideal, residual and completion quotients

- `Zeta23.OPICA.zero_ideal_eq_coordinate_power` — `Zeta23.OPICA.LocalQuotients`.
- `Zeta23.OPICA.truncated_taylor_quotient_equiv` — `Zeta23.OPICA.LocalQuotients`.
- `Zeta23.OPICA.completion_quotient_equiv` — `Zeta23.OPICA.LocalQuotients`.
- `Zeta23.OPICA.residual_congr_preserves_residue` — `Zeta23.OPICA.LocalObstruction`.
- `Zeta23.OPICA.finite_residual_products_preserve_residue` — `Zeta23.OPICA.LocalObstruction`.

Required content: Prove the actual holomorphic-germ ideals and quotient equivalences (existence of ring/linear equivalence with specified Taylor coordinates). Not substituted by an abstract isomorphism hypothesis. Residual class 1+(Z), any finite nonnegative power/product, exact residue and vanishing order of the difference.

### L3 — Repeated completions and normalization

- `Zeta23.OPICA.iterated_completion_leading_jet` — `Zeta23.OPICA.LocalObstruction`.
- `Zeta23.OPICA.double_completion_leibniz_factor` — `Zeta23.OPICA.LocalObstruction`.

Required content: Exact order p*m-1 for positive counts; factorial-normalized coefficient and binomial factor; correction term retained.

### L4 — Affine corrected finite composition

- `Zeta23.OPICA.affine_transport_corrected_eq` — `Zeta23.OPICA.AffineTransport`.
- `Zeta23.OPICA.affine_transport_leading_jet` — `Zeta23.OPICA.AffineTransport`.
- `Zeta23.OPICA.analytic_addition_can_cancel_completed_jet` — `Zeta23.OPICA.Counterexamples`.

Required content: Finite correction recursion and expanded suffix-product sum; corrected leading class, not unconditional preservation of raw output. Exact simple-pole/completion/background counterexample satisfying admitted hypotheses.

### L5 — Limit scope and residue continuity

- `Zeta23.OPICA.residue_continuous_of_circle_uniform` — `Zeta23.OPICA.ResidueLimits`.
- `Zeta23.OPICA.escaping_tail_keeps_residue` — `Zeta23.OPICA.ResidueLimits`.

Required content: Common meromorphic disk, only center pole, boundary uniform topology and quantitative radius bound; separate causal/safe-half-plane convergence counterexample.

### E1 — Logarithmic comparison inequality

- `Zeta23.OPICA.log_one_add_posPart_sub_le` — `Zeta23.OPICA.EnergyRate`.
- `Zeta23.OPICA.log_one_add_norm_sub_le` — `Zeta23.OPICA.EnergyRate`.

Required content: Actual logarithmic inequalities for all real/complex inputs; norm of the difference is the error.

### E2 — Subexponential additive rate preservation

- `Zeta23.OPICA.subexpAlong_add` — `Zeta23.OPICA.EnergyRate`.
- `Zeta23.OPICA.subexpAlong_mul` — `Zeta23.OPICA.EnergyRate`.
- `Zeta23.OPICA.subexpAlong_const_smul` — `Zeta23.OPICA.EnergyRate`.
- `Zeta23.OPICA.rate_congr_of_subexp_error` — `Zeta23.OPICA.EnergyRate`.
- `Zeta23.OPICA.posRate_congr_of_subexp_error` — `Zeta23.OPICA.EnergyRate`.
- `Zeta23.OPICA.rate_limsup_liminf_congr` — `Zeta23.OPICA.EnergyRate`.

Required content: Same positive cofinal schedule, full limit difference and equality of extended limsup/liminf; subexponential functions form a constant-scalar vector space, not an ideal of all sequences.

### E3 — Tempered scaling and inverse cost

- `Zeta23.OPICA.rate_congr_of_tempered_scale` — `Zeta23.OPICA.EnergyRate`.
- `Zeta23.OPICA.posRate_congr_of_positive_tempered_scale` — `Zeta23.OPICA.EnergyRate`.

Required content: Nonzero scaling with magnitude AND inverse cost; positive-part variant requires positive real orientation.

### E4 — Growing-chain accumulated budget

- `Zeta23.OPICA.affine_chain_expansion` — `Zeta23.OPICA.Composition`.
- `Zeta23.OPICA.affine_chain_budget` — `Zeta23.OPICA.Composition`.
- `Zeta23.OPICA.rate_congr_of_accumulated_budget` — `Zeta23.OPICA.Composition`.

Required content: Exact chain expansion and all suffix products; variable-depth conclusion consumes accumulated product/error, not pointwise fixed-stage bounds.

### E5 — Quiet cofinal observations

- `Zeta23.OPICA.quiet_cofinal_rate_zero` — `Zeta23.OPICA.Composition`.

Required content: Generic conditional full-rate consumer on the same observation; no production of quiet windows or proof of native J5.2/MS1.

### C1 — Faithful quotient map criterion

- `Zeta23.OPICA.quotient_map_injective_iff` — `Zeta23.OPICA.Composition`.
- `Zeta23.OPICA.faithful_transfer_comp` — `Zeta23.OPICA.Composition`.

Required content: Actual quotient map induced by a background-respecting linear map; injectivity iff preimage equality; composition.

### C2 — Typed finite-path nonvanishing

- `Zeta23.OPICA.obstruction_path_nonzero` — `Zeta23.OPICA.Composition`.
- `Zeta23.OPICA.implication_path_nonzero` — `Zeta23.OPICA.Composition`.

Required content: Dependent state/carrier path, preserved admissibility and commuting/zero-reflecting maps or proved nonvanishing implications; finite induction only.

### A1 — Explicit divisor bounds

- `Zeta23.OPICA.divisor_count_submultiplicative` — `Zeta23.OPICA.DivisorBounds`.
- `Zeta23.OPICA.divisor_count_square_le` — `Zeta23.OPICA.DivisorBounds`.
- `Zeta23.OPICA.divisor_count_harmonic_sum_le` — `Zeta23.OPICA.DivisorBounds`.
- `Zeta23.OPICA.divisor_count_sqrt_sum_le` — `Zeta23.OPICA.DivisorBounds`.

Required content: Positive order and indices, X>=1; actual ordered-factorization counts and explicit order dependence; no asymptotic divisor bound premise.

### A2 — Native low-mask and mixed-term bounds

- `Zeta23.OPICA.primitive_mask_partition` — `Zeta23.OPICA.PrimitiveMasks`.
- `Zeta23.OPICA.low_primitive_bilinear_bound` — `Zeta23.OPICA.DivisorMask`.
- `Zeta23.OPICA.masked_typeI_mixed_bound` — `Zeta23.OPICA.DivisorMask`.
- `Zeta23.OPICA.masked_typeI_square_bound` — `Zeta23.OPICA.DivisorMask`.
- `Zeta23.OPICA.balanced_energy_comparison` — `Zeta23.OPICA.DivisorMask`.

Required content: Positive indices, gcd-reduced max mask, real cutoff, low includes diagonal; actual finite double-sum/integral partition under measurable/integrable source hypotheses. Full A2 coefficient and source hypotheses, with explicit 4*W*V^2*B*(1+log B)^(2*l-2)*(1+T)^(l*l), repeated indices retained; no assumed copy of the conclusion.

### A3 — Lawful regrouped-mask adapter

- `Zeta23.OPICA.mask_regrouping_difference` — `Zeta23.OPICA.DivisorMask`.
- `Zeta23.OPICA.regrouped_mask_rate_congr` — `Zeta23.OPICA.DivisorMask`.

Required content: Two exact scalar expansions, two independently bounded low-mask terms and correct high-mask difference; no mask equality inferred from unmasked field equality.

### B1 — Weighted Laplace holomorphy and pole exclusion

- `Zeta23.OPICA.laplace_holomorphic_of_weighted_L2` — `Zeta23.OPICA.WeightedLaplace`.
- `Zeta23.OPICA.laplace_iteratedDeriv_bound_of_weighted_L2` — `Zeta23.OPICA.WeightedLaplace`.
- `Zeta23.OPICA.no_visible_pole_of_weighted_L2` — `Zeta23.OPICA.WeightedLaplace`.

Required content: Actual weighted L2 norm and integral; strict half-plane; factorial derivative bound and legitimate source-identified connected-domain continuation.

### B2 — Range separation by an actual annihilator

- `Zeta23.OPICA.range_distance_of_annihilator` — `Zeta23.OPICA.RangeSeparation`.
- `Zeta23.OPICA.not_mem_rangeClosure_of_annihilator` — `Zeta23.OPICA.RangeSeparation`.

Required content: Bounded operator, nonzero continuous annihilator, actual nonzero pairing, closure and exact functional norm denominator.

### O1 — Recovery after projection

- `Zeta23.OPICA.observation_factors_iff_ker_le` — `Zeta23.OPICA.ObservationCompatibility`.
- `Zeta23.OPICA.contrast_cannot_recover_sum` — `Zeta23.OPICA.Counterexamples`.

Required content: Existence of linear recovered functional on range iff kernel inclusion. Algebraic finite-dimensional result does not imply uniform norm control. Concrete contrast annihilates the all-ones vector while the target sum does not, for positive dimension.

### O2 — Gram-rank and operator-norm controls

- `Zeta23.OPICA.gram_integral_posSemidef` — `Zeta23.OPICA.ObservationCompatibility`.
- `Zeta23.OPICA.gram_integral_not_rank_one` — `Zeta23.OPICA.Counterexamples`.
- `Zeta23.OPICA.single_vector_bound_not_operator_bound` — `Zeta23.OPICA.Counterexamples`.
- `Zeta23.OPICA.offDiagonal_mask_not_posSemidef` — `Zeta23.OPICA.Counterexamples`.

Required content: Well-defined finite-dimensional Hermitian Gram integral is PSD; no rank-one inference. Actual rank-two Gram integral with determinant 1/12; a chosen-vector estimate fails to bound other directions; off-diagonal mask can be indefinite.

### O3 — Finite compatibility dual certificate

- `Zeta23.OPICA.incompatible_iff_left_annihilator` — `Zeta23.OPICA.ObservationCompatibility`.
- `Zeta23.OPICA.range_distance_eq_annihilator_sup` — `Zeta23.OPICA.ObservationCompatibility`.
- `Zeta23.OPICA.seven_samples_six_coefficients_consistent` — `Zeta23.OPICA.Counterexamples`.

Required content: Finite complex compatibility matrix, conjugate adjoint, left-null pairing and norm-one dual distance formula; handles zero residual/dimension cases. Seven sampled data from one degree-five polynomial are compatible with six coefficients, with explicit witness.

### O4 — Equivalent observations preserve compatibility

- `Zeta23.OPICA.compatibility_under_invertible_left_map` — `Zeta23.OPICA.ObservationCompatibility`.
- `Zeta23.OPICA.solutions_preserved_under_left_map` — `Zeta23.OPICA.ObservationCompatibility`.

Required content: Exact equality of solution sets under invertible left map; inclusion only for a general left map.

### H1 — Signed sharp-gap separator

- `Zeta23.OPICA.signed_sharp_gap_separator` — `Zeta23.OPICA.SignedHeatSeparator`.

Required content: Full locally finite real signed measure with linear total-variation growth, distributional Fourier selfduality, exact open unit gap and off-lattice positivity. No missing analytic conclusion assumed as certificate.

### H2 — Global negative off-lattice mass budget

- `Zeta23.OPICA.signed_gap_negative_mass_budget` — `Zeta23.OPICA.SignedHeatSeparator`.

Required content: Same legitimately proved signed pairing, global negative mass and finite E_(R,d) positive mass, correct 4*d^2/(pi^2*R^2).

### H3 — Involution commutator parity

- `Zeta23.OPICA.commutator_anti_invariant` — `Zeta23.OPICA.Involution`.
- `Zeta23.OPICA.commutator_selfdual_projection_zero` — `Zeta23.OPICA.Involution`.

Required content: Linear involution and common domain; actual selfdual input; commutator anti-invariant and selfdual projection zero.

### H4 — Fejer identity with affine completion correction

- `Zeta23.OPICA.fejer_floor_formula` — `Zeta23.OPICA.FejerCompletion`.
- `Zeta23.OPICA.fejer_nativeCompletion_pointwise` — `Zeta23.OPICA.FejerCompletion`.
- `Zeta23.OPICA.fejer_completion_affine_identity` — `Zeta23.OPICA.FejerCompletion`.
- `Zeta23.OPICA.fejer_logInteger_oneSidedDerivatives` — `Zeta23.OPICA.FejerCompletion`.

Required content: Convergent sinc lattice sum/Poisson pairing, floor endpoints, current native completion, mandatory rational affine correction and distinct one-sided cusp derivatives.

### NATIVE — Existing-source native adapters

- `Zeta23.OPICA.native_completed_input_obstruction_order` — `Zeta23.OPICA.NativeJetAdapter`.
- `Zeta23.OPICA.native_completed_input_obstruction_jet` — `Zeta23.OPICA.NativeJetAdapter`.
- `Zeta23.OPICA.native_completed_input_obstruction_ne_zero` — `Zeta23.OPICA.NativeJetAdapter`.
- `Zeta23.OPICA.native_range_distance_lower` — `Zeta23.OPICA.NativeJetAdapter`.
- `Zeta23.OPICA.step123_output_opica_view_correct` — `Zeta23.OPICA.NativeJetAdapter`.
- `Zeta23.OPICA.step123_eachPhase_opica_consumer` — `Zeta23.OPICA.NativeJetAdapter`.
- `Zeta23.OPICA.native_original_drive_low_mask_bound` — `Zeta23.OPICA.NativeArithmeticAdapter`.

Required content: Instantiate from existing actual physical transform, actual zero/right-zero/damping and one same-state generated output. Only off-line-zero inputs from established producer; no extra caller source nonzero-jet or range upper premise. Actual original j-drive with proof of continuity, boundedness and positive causal gap; finite palette compensation and literal translate mask. Higher-source uniformity and global tail cancellation not asserted.

### 5.1 Type/claim anti-substitution rules

A root is rejected if it has changed its intended conclusion into an input hypothesis, generalized away the native object, strengthened a generic premise to the exact desired conclusion, introduced a phantom source class with no native instance, or restricted an infinite measure theorem to a finite special case without recording the missing scope.

The expected type is a Lean expression checked against the real declaration. Store its human-readable full type and lossless expression DAG. The audit must inspect dependencies in **types, values and structure fields**, not just names in the theorem body. `#print axioms` alone cannot detect a malicious or accidental RH-strength **theorem parameter**, so exact type and constructor review is separate and mandatory.

All 38 historical corrections are cross-referenced to preventing types, checks or documentation. Not every correction is itself a theorem; for example, an absent native source theorem stays absent rather than being encoded as an axiom.

## 6. Compiler and evidence wiring

### 6.1 Existing helpers that can be reused

`Zeta23.RHRC.DeclarationDependencyExport` already exposes compiler dependency extraction including TYPE/VALUE/STRUCTURE uses. `Zeta23.RHRC.SourceCandidateResolution` already resolves exact module/kind/name candidates against the environment. Reuse their public commands from `OpicaBindings`.

The lossless expression-DAG helper in the old `Step123OutputBindings.lean` is **private**. Do not pretend it is a public reusable API or edit the frozen 44-field exporter to expose it. Create the source-attributed `OpicaTypeExprExport.lean` adaptation. Reuse the existing read-only `routes/R003_ccm_bridge/post290/lean_expr_dag.py` decoder where compatible, with a new OPICA parser and explicit schema. The old `build_formal_receipt.py` is tied to the 44-field contract and must not be relabeled as an OPICA receipt builder.

### 6.2 Required compiler receipt

The OPICA receipt must contain:

- actual checkout commit and tree; requested PR head, base and synthetic merge identities kept distinct;
- toolchain, Mathlib pin, runtime versions and exact commands/exit codes;
- hashes of every new source, defining module and governing manifest;
- every primary root's exact name, module, kind, full type and lossless type-expression DAG;
- structure/constructor full types and transitive type/value/structure dependencies;
- `#print axioms` results and explicit allowed-axiom checks;
- actual typed consumer results and paper-clause coverage;
- protected old source and claim-object comparisons;
- outputs/dispositions of finite controls, never promoted to analytic proof;
- full job/run/attempt identifiers for the execution being summarized.

Allow only the established standard axiom set `propext`, `Classical.choice`, `Quot.sound` for mathematical roots. Reject `sorryAx`, project axioms, `Lean.ofReduceBool`/native-compiler trust additions and equivalent bypasses. A bounded unsafe helper used solely to serialize an environment is an AUDIT_ONLY implementation detail; no mathematical proof may depend on it. Fail closed if serialization truncates, a name resolves ambiguously, a type mismatches or a public declaration escapes enumeration.

Receipts are artifacts emitted **outside the tracked repository tree**. Do not commit a receipt claiming the SHA of its own future commit. The committed graph products use the existing deterministic content-binding scheme; the exact checked head is an external CI receipt.

### 6.3 Registry integration sequence

Implement and compile the mathematical roots and their typed consumers first. During work-in-progress, record them as unimplemented/proposed in the OPICA-local specification, not as globally proved claims. Once exact proof/type/axiom review succeeds, append the corresponding claims, binding rows and direct imports together. Rebuild the global registered audit and regenerate its compiler graph receipt.

Full PR acceptance still requires all 76 planned roots and every listed subclause. The existing global linter remains unchanged and must pass. It is not acceptable to silence it by changing its expected OPEN set or skipping a missing theorem.

## 7. Generated products: required refresh, not hand editing

Run the existing transactional producer unchanged:

```sh
python research/RHRC/tools/materialize_derived_state.py --write
python research/RHRC/tools/materialize_derived_state.py --check
```

The existing pipeline orders registered compiler dependencies, graph building, source-candidate exactification, FFBBP assurance, source-only dependency export, contact-quotient views and OoL phase-atlas production. It snapshots and restores the five declared generated directories on failure.

**Stage new authoritative files before regeneration.** The source census uses tracked paths (`git ls-files`). An untracked new module or documentation file can be absent from a generated graph even if it exists on disk. Freeze and stage the intended source/config/document input before invoking the producer, then stage only its deterministic byte-changed outputs. Any later authoritative change requires regeneration again.

The exact 62 current outputs below are the generator allowlist. A fresh execution may leave some byte-identical; do not manufacture a diff or rewrite historical snapshots to satisfy a count.

```text
research/RHRC/ffbbp/generated/RHKG_CANDIDATE_REDUCTION_ASSURANCE.json
research/RHRC/graph/compiler/REGISTERED_DECLARATION_DEPENDENCIES.jsonl
research/RHRC/graph/generated/CONTACT_QUOTIENT_DECLARATION_DEPENDENCIES.jsonl
research/RHRC/graph/generated/CONTACT_QUOTIENT_VIEW.json
research/RHRC/graph/generated/DEPENDENCY_BRIDGE_FRONTIERS.json
research/RHRC/graph/generated/DEPENDENCY_COHORT_ATOMS.json
research/RHRC/graph/generated/DEPENDENCY_COHORT_OVERLAP.json
research/RHRC/graph/generated/DEPENDENCY_KERNEL_ATLAS.json
research/RHRC/graph/generated/DEPENDENCY_KERNEL_QUOTIENT.json
research/RHRC/graph/generated/DEPENDENCY_PROJECTION_FRONTIERS.json
research/RHRC/graph/generated/DEPENDENCY_PROJECTION_QUOTIENTS.json
research/RHRC/graph/generated/DEPENDENCY_PROJECTION_SUMMARY.json
research/RHRC/graph/generated/DEPENDENCY_SIGNATURE_CLASSES.json
research/RHRC/graph/generated/DOCUMENT_SEMANTIC_CLOSURE.json
research/RHRC/graph/generated/ENTRYPOINT_REACHABILITY.json
research/RHRC/graph/generated/MODULE_SEMANTIC_CLOSURE.json
research/RHRC/graph/generated/REPOSITORY_COVERAGE.json
research/RHRC/graph/generated/THEOREM_CLAIM_MAP.json
research/RHRC/graph/generated/THEOREM_DEPENDENCY_CLOSURE.json
research/RHRC/graph/generated/UNRESOLVED_GRAPH_ITEMS.json
research/RHRC/graph/generated/lean_declarations.jsonl
research/RHRC/graph/generated/lean_modules.jsonl
research/RHRC/graph/generated/lean_source_declarations.jsonl
research/RHRC/graph/generated/registry_nodes.jsonl
research/RHRC/graph/generated/relations/relations-0.jsonl
research/RHRC/graph/generated/relations/relations-1.jsonl
research/RHRC/graph/generated/relations/relations-2.jsonl
research/RHRC/graph/generated/relations/relations-3.jsonl
research/RHRC/graph/generated/relations/relations-4.jsonl
research/RHRC/graph/generated/relations/relations-5.jsonl
research/RHRC/graph/generated/relations/relations-6.jsonl
research/RHRC/graph/generated/relations/relations-7.jsonl
research/RHRC/graph/generated/relations/relations-8.jsonl
research/RHRC/graph/generated/relations/relations-9.jsonl
research/RHRC/graph/generated/relations/relations-a.jsonl
research/RHRC/graph/generated/relations/relations-b.jsonl
research/RHRC/graph/generated/relations/relations-c.jsonl
research/RHRC/graph/generated/relations/relations-d.jsonl
research/RHRC/graph/generated/relations/relations-e.jsonl
research/RHRC/graph/generated/relations/relations-f.jsonl
research/RHRC/graph/generated/repository_files.jsonl
research/RHRC/integration/generated/RH_CORE_SOURCE_ONLY_THEOREMS.jsonl
research/RHRC/integration/generated/SOURCE_CANDIDATE_RESOLUTION.jsonl
research/RHRC/integration/generated/SOURCE_CANDIDATE_SUMMARY.json
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-0.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-1.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-2.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-3.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-4.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-5.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-6.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-7.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-8.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-9.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-a.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-b.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-c.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-d.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-e.jsonl
research/RHRC/integration/generated/source_only_dependencies/SOURCE_ONLY_CANDIDATE_DEPENDENCIES-f.jsonl
research/RHRC/ool/generated/RHKG_OOL_PHASE_ATLAS.json
research/RHRC/ool/generated/RHKG_OOL_ROUTE_CONTACTS.jsonl
```

The manifest set was checked against `ALL_DECLARED_GENERATED_PRODUCTS` plus the registered compiler receipt path in the pinned graph producer. The old source-only and relation shard schemes remain unchanged.

The existing RHRC job checks committed freshness **before** any generator writes and rejects tracked or untracked drift. The new workflow must not “fix” stale files in CI and report the repaired checkout as if it had tested the submitted tree.

## 8. Workflow and all-job harvest

Create one new workflow with the five jobs below. Names are fixed by `WORKFLOW_CONTRACT.json`; an unfinished required job is not success.

| Job | Classification | Evidence produced |
|---|---|---|
| `opica-contract` | FORMAL VALIDITY GATE (static, not kernel proof) | Paths, sources, paper coverage, exact root inventory, graph roles and protected-state checks |
| `opica-formal` | FORMAL VALIDITY GATE | All modules and typed consumers compiled; complete compiler/type/axiom receipt |
| `opica-regression` | REGRESSION GATE | Frozen 5,112 controls reproduced; new contract/parser/mutation tests reported separately |
| `opica-dependency-delta` | RESEARCH-PRODUCING CHECK | Exact use-graph and coverage differences; no mathematical-equivalence inference |
| `opica-component-summary` | FORMAL VALIDITY GATE (component completeness) | Aggregated pass/fail dispositions and exact source identities; no independent-review or RH approval |

### 8.1 Triggers and privileges

Use `pull_request` to main, push to the named research branch and `workflow_dispatch`. Do not use `pull_request_target`. Use read-only repository permissions, `persist-credentials: false`, no secrets, no review bot approval, and no push step. The checkout SHA actually tested is read from Git and bound in every artifact. PR-head and synthetic-merge evidence are distinct even when their trees agree.

Use the immutable direct-action SHAs already present in the repository's guarded workflows:

```text
actions/checkout@11d5960a326750d5838078e36cf38b85af677262
actions/setup-python@a26af69be951a213d495a4c3e4e4022e16d87065
leanprover/lean-action@24581d74d674803a25a81b10b059c5c0cdd344c6
actions/upload-artifact@ea165f8d65b6e75b540449e92b4886f43607fa02
actions/download-artifact@d3f86a106a0bac45b974a628896c90dbdf5c8093
```

Record the runner image and Python runtime; use the repository's Python 3.14 line without adding dependencies for the standard-library checks. Mathlib cache use must be bound to its pin. Do not reuse untrusted project build outputs from unrelated PRs; a clean exact-source build of the new modules and consumers is required. Shell code must receive untrusted workflow values through validated environment variables, not splice them into command text.

### 8.2 Required commands and output contract

The following are the **specified future commands**, not commands executed in this specification turn. Implement each CLI with these flags and behavior; failure exits nonzero.

```sh
# ART is an existing writable directory outside the checkout, e.g. $RUNNER_TEMP/opica.
python research/RHRC/integration/opica/validate_contract.py \
  --phase preflight --base 97926d6a949fed7af0429a373b47abc772012834 \
  --output "$ART/contract.json"

lake build Zeta23.OPICA Zeta23.OPICA.Validation Zeta23.RHRC.OpicaBindings

# Explicit elaboration emits audit output even if Lake used current cached .olean files.
set -o pipefail
lake env lean Zeta23/RHRC/OpicaBindings.lean 2>&1 | tee "$ART/compiler.log"

python research/RHRC/integration/opica/build_receipt.py \
  --manifest research/RHRC/integration/opica/BUILD_MANIFEST.json \
  --roots research/RHRC/integration/opica/PUBLIC_ROOTS.json \
  --compiler-log "$ART/compiler.log" --output "$ART/formal_receipt.json"

python research/RHRC/integration/opica/check_exact.py \
  --output "$ART/exact_normal.json"
python -O research/RHRC/integration/opica/check_exact.py \
  --output "$ART/exact_optimized.json"
python -m unittest discover -s research/RHRC/integration/opica/tests -p 'test_*.py' -v
python -O -m unittest discover -s research/RHRC/integration/opica/tests -p 'test_*.py' -v
```

The supplied exact checker already uses explicit `verify` failures rather than bare Python assertions. Preserve this behavior when porting it and add `--output`; any new checks must also remain active under `python -O`. Preserve the old 5,112 cases and their group dispositions as the baseline; any additional controls have separately reported counts. Mutation tests must demonstrate actual rejection under both interpreter modes.

After global registry integration:

```sh
lake build Zeta23.RHRC.RegisteredClaimBindings \
  Zeta23.RHRC.DeclarationDependencyExport Zeta23.RHRC.SourceCandidateResolution
python research/RHRC/tools/registered_theorem_binding_lint.py
python research/RHRC/tools/run_suite.py --skip-derived-state
python research/RHRC/tools/materialize_derived_state.py --check
python research/RHRC/integration/opica/validate_contract.py \
  --phase release --base 97926d6a949fed7af0429a373b47abc772012834 \
  --formal-receipt "$ART/formal_receipt.json" --output "$ART/release_contract.json"
```

`--phase preflight` checks the declared specification without fabricating proof success; it cannot return a formal-complete status when roots are absent. `--phase release` requires the full compiler evidence, complete root/subclause coverage and registered/derived-state agreement. A per-wave working receipt may be incomplete, but the final component summary must not treat it as a release pass.

The proposed audit exporter reads only fixed repository manifests with validated paths and exact module/name fields. It must not execute arbitrary Lean snippets from JSON. Log marker counts and a terminating completeness record are required; partial logs or a failed pipe are never accepted as a receipt.

### 8.3 Existing workflows remain authoritative

The new component summary covers its own five jobs. The complete pre-merge research harvest must additionally enumerate **all** jobs actually attached to the final PR/head/merge run, including inherited workflows. Do not hard-code the old count of 55 and do not substitute a cached green run from another head.

`harvest_workflows.py` consumes full paginated run/check/job records and preserves all attempts. Resolve partial reruns by the existing effective-job discipline: retain the failed history and identify the exact superseding attempt, rather than choosing whichever success looks favorable. Every required new job must be completed/success. Skipped inherited jobs require an explicit, reviewed disposition; they are never silently counted as passed.

Write all scientific outcomes as they actually are: a successful replay may preserve a falsifier or an OPEN obligation. `opica-dependency-delta` reports new uses, shared dependencies and changed coverage; it does not prove logical equivalence or elevate a research hypothesis.

The final independent review reads the new theorem types, proof assumptions and source consumers. This workflow cannot self-sign that review. No old PR292 44-field approval, D2 result or manual acceptance is repurposed as OPICA approval.

## 9. Build sequence and commit plan

1. **Freeze the contract.** Add the OPICA-local specifications, exact paper inputs, baseline protection and test harness contracts. Establish all typed goals before proof promotion. Keep incomplete status explicit.
2. **Core local/energy/linear algebra.** Prove the witness and local lemmas, affine correction, log/rate calculus, quotient/path composition, recovery and finite compatibility results. Add the relevant exact Lean counterexamples.
3. **Analytic and arithmetic foundations.** Prove the genuine quotient construction, contour limit, ordered-factorization counting, finite source/mask integrability, weighted Laplace derivative bound and range separation. Do not skip their heavy subclauses.
4. **Native source consumers.** Build the actual fixed-source jet and arithmetic adapters and one same-packet typed consumer. Keep old files untouched and document the exact parameter restrictions.
5. **Fourier/measure layer.** Complete the locally finite signed-measure embedding, Fourier pair/regularization, signed separator and Fejer identities. Compile H3 early if useful, but final H1/H2/H4 remain mandatory.
6. **Audit and register.** Finish every typed consumer, exporter and mutation control; review exact types/axioms; add the 76 global supporting bindings atomically; add trust/standalone roles and run-suite hooks.
7. **Materialize and clean checkout.** Stage authoritative inputs, run the unchanged full producer, commit generated byte changes, and validate from a clean checkout with no generator writes. Bind CI artifacts to that exact source.
8. **Harvest and post-green pass.** Read the proofs and every job; compare the old dispositions; complete the OPICA post-green report with actual new facts, upstream/downstream implications and precise remaining gaps. Re-materialize if this tracked document changes, and rerun the affected exact-head gates.

These are dependency checkpoints inside the proposed full PR, not permission to merge a partially covered paper under a full-completion title. A separate explicitly reduced PR is a scope decision, not an implementation shortcut.

## 10. Acceptance, rollback boundaries and risk register

**Required for full acceptance:** all 25 families and their stated subclauses; all 76 semantic roots; public definition/structure inventory; native consumers; exact type/axiom closure; all static and mutation controls; old protected semantics; byte-current derived state; all required workflow dispositions; explicit independent mathematical review; an actual post-green research record.

**Not enough:** `lake build` on the old default target, one #check of a structure with unproved fields, 5,112 Python controls, a theorem carrying its conclusion as a premise, a graph with the right labels, or an axiom-clean proof whose type secretly assumes a native closing upper.

| Risk | Required prevention |
|---|---|
| Punctured identity used at a totalized singular value | Explicit analytic representative and neighborhood type checks |
| Completion/probe confusion | Distinct operators and source transforms in native adapter signatures |
| Derivative versus coefficient factorial error | Exact expected jet type and multiplicity-phase fixture |
| Fixed-stage estimate promoted to moving rate | Same schedule plus complete source and propagated-cost hypotheses |
| Pair mask changed by kernel absorption | Two separately bounded low-mask budgets and exact difference identity |
| Infinite locally finite measure silently made finite | Faithful signed-measure/distribution representation with preserved growth class |
| All-ones projection removes the target | Kernel-recovery theorem and explicit contrast counterexample |
| New global OPEN claim breaks existing registry contract | Pending scope stays local; append only checked theorem statements |
| New source makes RHKG snapshots stale | Stage tracked inputs and run full transaction, then read-only freshness check |
| Cached or truncated audit masquerades as compiler evidence | Exact source manifest, full type DAG, terminator, exit status and clean validation |
| New audit helper becomes part of a proof | One-way imports; normal facade excludes RHRC/audit modules |
| Extra public helper escapes authority audit | Compiler environment enumeration, not just primary-root list |
| Old native semantics change through “integration” | Hash-protect old proof files, claim objects, D2/review contracts and old root closure |

No toolchain migration or generic relaxation of existing linters is pre-authorized. A real pinned-API or proof difficulty must be reported with the exact missing lemma and a reviewed specification change, not hidden by a new axiom or a weakened statement.

## 11. What this specification has actually validated

The executable specification validator checks snapshot identities, proposed file absence, edit-base hashes, new import resolution, combined import-cycle freedom, full paper/root coverage, old import reachability, standalone-role additions, unchanged old trust classification, new path classifications and the exact generated-output set. The full result is in `OPICA_PR_SPEC_VALIDATION_2026-10-21.json`.

The inherited 5,112-case exact checker was also replayed unchanged under normal Python and `python -O`: both passed with the same case groups, fixtures and checker hash as the paper receipt. This is a regression replay, not new analytical proof. The current specification validator does not invoke Lean, materialize the real derived graph, create a branch, insert registered claims or open a PR. It validates the **build design**, not the proposed proofs or future artifacts.

The mathematically useful outcome of a completed implementation would be exact formal preservation, transfer and incompatibility lemmas with real native consumers. It would not establish the missing independent upper, a universal no-go theorem, the native heat-defect construction, or RH. Those remain separately OPEN.

## 12. Evidence and source register

Source-derived requirements and implementation decisions are distinguished throughout. The OPICA paper and its implementation contract supply the 25 theorem scopes and claim firewall. The finer module split, route-less primary-root registration, separate facade, five-job workflow and exact file footprint are the proposed integration design from this audit.

Pinned repository sources used to determine integration:

- [lakefile.toml](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/lakefile.toml) — Existing library and default root; no new library needed.

- [lean-toolchain](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/lean-toolchain) — Pinned compiler.

- [lake-manifest.json](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/lake-manifest.json) — Pinned dependency realization.

- [.github/workflows/rhrc.yml](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/.github/workflows/rhrc.yml) — Existing compiler/registry/derived-state checks.

- [.github/workflows/rhrc_post290_step123_output.yml](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/.github/workflows/rhrc_post290_step123_output.yml) — Frozen historical explicit component workflow.

- [.github/workflows/rhrc_post292_one_shot_rhkg_refresh.yml](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/.github/workflows/rhrc_post292_one_shot_rhkg_refresh.yml) — Existing pinned actions and guarded materialization precedent.

- [.github/workflows/rhrc_post292_release_candidate.yml](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/.github/workflows/rhrc_post292_release_candidate.yml) — Historical receipt/review security precedent; not modified.

- [research/RHRC/tools/registered_theorem_binding_lint.py](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/research/RHRC/tools/registered_theorem_binding_lint.py) — Exact registry/bindings/imports and OPEN-set agreement.

- [research/RHRC/tools/materialize_derived_state.py](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/research/RHRC/tools/materialize_derived_state.py) — Transactional complete generated-state pipeline.

- [research/RHRC/graph/build.py](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/research/RHRC/graph/build.py) — Tracked source census, exact standalone set and generated products.

- [research/RHRC/graph/FILE_CLASSES.json](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/research/RHRC/graph/FILE_CLASSES.json) — First-match trust rules.

- [research/RHRC/graph/SEMANTIC_CLOSURE_CONFIG.json](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/research/RHRC/graph/SEMANTIC_CLOSURE_CONFIG.json) — Explicit standalone roles.

- [Zeta23/RHRC/DeclarationDependencyExport.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/Zeta23/RHRC/DeclarationDependencyExport.lean) — Public compiler dependency exporter.

- [Zeta23/RHRC/SourceCandidateResolution.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/Zeta23/RHRC/SourceCandidateResolution.lean) — Exact source/module/kind resolver.

- [Zeta23/RHRC/Step123OutputBindings.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/Zeta23/RHRC/Step123OutputBindings.lean) — Private expression serializer and frozen old receipt.

- [research/RHRC/routes/R003_ccm_bridge/post290/lean_expr_dag.py](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/research/RHRC/routes/R003_ccm_bridge/post290/lean_expr_dag.py) — Reusable read-only expression DAG validation.

- [Zeta23/ExceptionalZero/NativeActualInputZeroJets.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/Zeta23/ExceptionalZero/NativeActualInputZeroJets.lean) — Actual input physical-neighborhood equality and exact jet.

- [Zeta23/ExceptionalZero/Step123CompleteOutput.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/Zeta23/ExceptionalZero/Step123CompleteOutput.lean) — Same-state output and separate cofinal phases.

- [Zeta23/CCM/NativeIntegerDriveFiniteOrderBounds.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/Zeta23/CCM/NativeIntegerDriveFiniteOrderBounds.lean) — Existing original-drive decay fact.

- [Zeta23/CCM/OriginalSincNativeSource.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/Zeta23/CCM/OriginalSincNativeSource.lean) — Actual j source/field/history definitions.

- [Zeta23/CCM/NativePositiveCompletionComplexLaplace.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/Zeta23/CCM/NativePositiveCompletionComplexLaplace.lean) — Actual completion and continuation domain.

Pinned Mathlib distribution foundation checked through the connector: [`TemperedDistribution.lean`](https://github.com/leanprover-community/mathlib4/blob/51e6992efd06126df61a496bebf8f49482a4e129/Mathlib/Analysis/Distribution/TemperedDistribution.lean), blob `3bbfd124249ffd78c7ab943d7e4f1475f80e2373`. It supplies the tempered-distribution/Fourier foundation, not the new signed separator proof. No claim is made that every future import or tactic in the full formalization was elaboration-tested today.

Paper source release: `OPICA_Paper_Construction_v1_0_2026-10-21.md`, SHA-256 `6c6d43857636d635c6da018b38046b19cdff4bee780840ac67ae81d32bec1777`; implementation contract SHA-256 `ea8c59913b2733b4758b2d7cbdbc698d88dd5570d3d24f057a117ae12398a21a`; theorem/audit ledger SHA-256 `ff8a163e47208996b0a4ef70197414461f956aee45c470c42b56b9386178c08f`.

**Final state of this turn:** exact file/registry/import/CI specification prepared; no implementation or new theorem authority. RH and Step 4 remain OPEN.
