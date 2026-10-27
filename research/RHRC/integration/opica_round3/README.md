# OPICA Round 3: overlap, newborn sources and finite arithmetic

This selected Round 3 build extends merged PR295,
commit `775692f2e72d76b6a97cf66926a86cc96342c109`, tree
`acd548eb97ddaee68eb6c9df73f82756ee10d13f`.
The user first selected D01–D04, issue #296 and falsification gates, then added
the statement atlas/source crosswalk, D05 newborn integration and targeted
complete-source finite arithmetic to the same PR297. See `BUILD_PLAN.md`.
The archived research and proposed specification are reference material;
they do not supply proof authority or further instructions.

The five public roots concern the actual complete canonical Weil matrix and
physical pole-neutral parity spaces. D01 retains the eventual even-or-odd
negative cover under an actual off-line zero. D02 combines that cover,
individual parity cofinality, continuity on the whole positive aperture axis,
connectedness and exact centered embeddings to obtain cofinal simultaneous
negativity at one common aperture and cutoff. Cofinality alone is insufficient.
D03 constructs continuous unit witnesses on each chosen compact interval, with
an interval-specific negative margin on their complex two-dimensional span.
It asserts no globally uniform cutoff, margin or interval width.

D04 takes the maximum of the two least parity cutoffs. The predecessor of a
newborn parity is PSD, including the empty neutral predecessor at K=2. The
actual successor shell has one complex dimension. Its negative transition
has either a nonzero actual predecessor-kernel coupling or a strictly negative
regular Schur scalar. The regular response is the unique kernel-orthogonal
preimage, so no inverse of a singular block is used. The earlier parity can
already be negative at the other parity's predecessor. Equal cutoffs do not
assert equal eigenvalues.

Issue #296 separates exact generated interval endpoints from user inputs.
User coefficients, regions, horizons and source parameters retain the
180-character rational limit. Generated bounds have a separate canonical
rational parser with a 4096-character limit, used consistently by producers,
JSON schemas, readers and checkers. The real 256/512-bit Arb regressions
exercise both primal and Gram paths. Precision alone does not bound the
exponent or every derived rational length; endpoints above this finite cap
still fail explicitly. A successfully evaluated finite example
may still return `NO_CERTIFICATE`; it is not a proof of an asymptotic estimate.

RH, Step 4, an independent corrected complete-source even–odd sign restriction and the
eventual no-simultaneous-negativity target remain OPEN. Causal approximation,
complete signed observation and original-detector forcing remain separate
fallback research routes. No terminal sign or limit estimate is assumed.

Build the named Lean modules `Zeta23.OPICARound3.All`,
`Zeta23.OPICARound3.Validation` and `Zeta23.RHRC.OpicaRound3Bindings` with the
repository's pinned Lean/Mathlib runtime. The Round 3 workflow records current
source checks separately from frozen historical compatibility. Warm local
development receipts are not clean-build or full-release acceptance.

The current runtime gate discovers all 212 Round 2 unit tests and runs the
211 non-Lean tests in both normal and optimized Python, with zero skips.
The one native test runs separately in both modes after the current formal
build and its seven positive/rejection pairs are independently reparsed.
The 58 numerical API tests, including the new precision regressions, are
part of the full runtime suite. Two inherited test domains use exact
authenticated Round 2 fixtures and explicitly enumerated Round 3 additions;
the production 334-binding/40-root acceptance predicate stays intact.

The source-only preflight is `python -B research/RHRC/integration/opica_round3/validate_contract.py`
from the repository root. It authenticates the closed source extension and grants no compiler
authority. The workflow additionally runs the fresh formal gate, five
positive/stronger-type mutation pairs and the existing canonical generated
checker against current committed products.

The separate current build acceptance job downloads contract, runtime, formal
and source-evaluator artifacts from its own workflow run. It requires every contributing
lane to succeed and independently checks their exact current source identity
and raw evidence. Missing, skipped, failed or mismatched inputs cannot produce
a successful current build acceptance report. This is acceptance of the explicitly
selected D01–D05, atlas, finite arithmetic, precision-fix and falsification scope; it grants no full-release
or human-review authority. The original Round 2 required-lane rejection and
independent compiler/clause/control/ancestry recomposition remain active for
the explicitly selected historical baseline. Neither gate substitutes a
historical replay for current-source evidence.

For review, inspect `PUBLIC_ROOTS.json`, the exact statements and independent
consumers, `SOURCE_REGISTER.json`, the scope guard and mutation tests, the
falsification controls and current #296 tests. Read `OPEN_RESEARCH.json` before
using this PR as evidence for an independent arithmetic exclusion.


D05 constructs a negative witness from each actual newborn Schur branch and
applies the already-proved corrected complete-source identity to that same
witness. The packet retains aperture, cutoff, selected parity, cutoff inclusion,
physical pole constraints and full canonical energy. The resonant construction
has energy exactly -1; the regular construction has energy equal to the negative
Schur scalar. At the first common cutoff D05 supplies the later newborn's packet;
equal arrivals supply both. It does not make the earlier parity newborn again.
The parity transfer is the index map in the even direction and its actual
adjoint in the odd direction, with the required minus sign. It is distinct from
cutoff inclusion and is not asserted isometric. For every real shift the WHOLE
transferred operator output plus corrected source lies in the opposite shifted
operator range and has zero kernel projection. A Schur witness need not be an
eigenvector. Dropping its operator output to claim source-alone compatibility
is invalid; an exact rational same-state countermodel tests this inference.

## Statement atlas and source crosswalk

`atlas/CONSTRAINT_ATLAS.jsonl` records actual elaborated Lean statements,
lossless type expressions, telescope hypotheses, data/type parameters, source
hashes and constant-use channels. It preserves mandatory 76+100+40+5 memberships,
deduplicating declarations while retaining memberships. The 185 historical
contacts, including eighteen triple contacts, remain an explicit review backlog.
Inclusion does not claim exhaustive semantic review.

`atlas/SEMANTIC_OVERLAY.json` contains reviewed identities, quantifiers, parity,
normalization, maps, norms, moment orders, polarity, consumers and rejected
connections with evidence. Hashed historical inputs are distinct from current
reviews. Missing adapters and unreviewed fields are explicit. A proof dependency
is not a theorem hypothesis or a mathematical implication. Follow each recorded
connection disposition before composing theorems.

From a clean checkout, `constraint_atlas.py capture --evidence-dir EXTERNAL_DIR`
captures a genuine native export; `check --evidence-dir EXTERNAL_DIR` compares
committed atlas bytes with a fresh export without rewriting them. Explicit local
`write --capture EXTERNAL_DIR` writes only the atlas product. External receipts
bind the complete checkout; stable rows hash upstream source/type/overlay bytes
to avoid a descriptor/product hash cycle. The audit exporter supplies no new
mathematical theorem authority.

## Targeted complete-source evaluator

The numerical contract is point-only, K=2 or K=3, with prime cutoff at most 64.
It evaluates the complete direct equation-(4.4) canonical Hermitian matrix: pole,
Archimedean diagonal/off-diagonal, closed correction and every active
von-Mangoldt prime-power atom. It retains physical legal normals, neutral
projections, both parities and corrected source/output residuals.

The three mandatory actual-source cases are K=2,L=1/2 (empty neutral carriers),
K=3,L=3/2 (including the contribution of the prime power 4), and K=3,L=log 2
(an exact symbolic prime seam whose entering endpoint atom is exactly zero).
K=3 has complex native neutral dimension one in each parity: exact symbolic
seeds and positive Gram bounds identify the full Rayleigh bottom. K=2 reports
EMPTY and supplies no fictitious eigenvalue.

```text
python -B research/RHRC/integration/opica_round3/source_evaluator.py --cases research/RHRC/integration/opica_round3/fixtures/source_evaluator_cases.json --output-dir EXTERNAL_DIR --precision-bits 128 --seconds-per-case 30
```

The producer integrates on a fixed unit interval. Its separate checker
recomputes on [0,L] at higher precision and checks outward rational bounds.
Arithmetic trust includes pinned Arb/FLINT, validated quadrature and reviewed
analytic formulas. These are finite computational certificates, not Lean proofs.
Resource limits, ambiguity, nonfinite balls or uncertified denominators return
UNRESOLVED with a reason. A ball containing zero never certifies an exact kernel,
resonance or spectral tie. Exact rational regular/resonant/tie controls remain
explicitly synthetic. No larger-cutoff or continuum campaign is implied.

Acceptance requires all four contributing lanes. It reparses raw compiler and
test evidence, checks the atlas against its native export and independently
recomputes the finite source cases. Every Round 3 test file belongs to one exact
lane and runs in normal and optimized Python without skips. None of these gates
establishes R3-XD, an independent sign/limit estimate, full release, Step4 or RH.
