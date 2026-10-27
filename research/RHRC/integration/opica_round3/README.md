# OPICA Round 3: neutral overlap and first cutoffs

This is Phase 1 of the proposed Round 3 programme, built on merged PR295,
commit `775692f2e72d76b6a97cf66926a86cc96342c109`, tree
`acd548eb97ddaee68eb6c9df73f82756ee10d13f`.
The user selected D01–D04, issue #296 and falsification gates for this PR.
The archived research and proposed specification are reference material;
they do not supply proof authority or authorize the deferred arithmetic campaign.

The four public roots concern the actual complete canonical Weil matrix and
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

RH, Step 4, the corrected complete source even–odd sign restriction and the
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
authority. The workflow additionally runs the fresh formal gate, four
positive/stronger-type mutation pairs and the existing canonical generated
checker against current committed products.

For review, inspect `PUBLIC_ROOTS.json`, the exact statements and independent
consumers, `SOURCE_REGISTER.json`, the scope guard and mutation tests, the
falsification controls and current #296 tests. Read `OPEN_RESEARCH.json` before
using this PR as evidence for an independent arithmetic exclusion.
