# Full native logarithmic-window rates — post-green research pass

24 October 2026. Base commit `59ff485551771c0ab6322562d18fb8e9d4166da4`,
tree `396665de3d14c2db60a4a85c646dd56d718f07ff`. The owner was editing
documentation/evidence when the receipt was sealed; its exact dirty status is
recorded. Imported mathematical sources and all staged bytes are individually
hashed. This report describes the independently compiled staged candidates;
production installation, subsequent exact-byte replay and ledger promotion
belong to the root owner. RH, Step 4 and the independent quiet upper remain OPEN.

## 1. What became formally true

The exact original two mathematical rate signatures compile under their correct
production module names with only `propext`, `Classical.choice`, `Quot.sound`:

\[
 \lim_{T\to\infty}\frac{\log(1+\int_{T-C\log T}^{T}|F_d(t)|^2dt)}{2T}=\Theta
 \quad(d\in\mathbb N,\ C>1),
\]

and, for every real cofinal sequence `T_n` and arbitrary integer orders with
`d_n log(d_n+2)/T_n→0`,

\[
 \lim_n\frac{\log(1+\int_{T_n-C\log T_n}^{T_n}|F_{d_n}(t)|^2dt)}{2T_n}=\Theta
 \quad(C>1).
\]

`F_d` is the literal `primeFieldFamily d`; `Theta` is the actual
`nativeZeroDisplacementSup`. There is no native-rate or no-zero premise. The
proof covers order zero, arbitrary actual zero multiplicity and `Theta=0`.
No positivity premise on every `T_n` was added: the proof uses `max(1,T_n)`
inside the genuine horizon adapter, then transfers back by eventual equality.
The fixed-source conclusion is a continuous real limit, proved through the
countably generated atTop filter, not an integer-horizon statement.

For the positive lower direction, one actual zero is chosen strictly above a
test displacement before the horizon limit. No rightmost zero is assumed.
Its multiplicity and derivative constant stay fixed while source orders may
vary. The exact source identity prices both signs of its logarithm. The A6
completed-input subtraction is proved eventually at most one half of its
actual leading term, rather than being discarded by assertion.

## 2. Workflow harvest

Immutable production-candidate receipt:
`staged/STAGED_RATE_COMPILER_RECEIPT_2026-10-24.json`, SHA-256
`cd43218db38479709cb21764a992870c791a1fb8e04b75269deeb69ce9210047`.

| Check | Disposition |
|---|---|
| Exact staged `NativeWindowRate.lean` | exit 0; fixed primary standard axioms |
| Exact staged `MovingSourceWindowRate.lean` | exit 0; MS1 primary standard axioms |
| Independent full physical consumer | exit 0; both full types, d=0, finite negative prefix, source logarithm signs, literal rate definition, Theta=0 |
| Omit MS1 slow-order hypothesis | expected exit 1, rejected at the missing original premise |
| Invoke fixed primary at C=1 | expected exit 1, rejected because the required strict inequality is false |

The receipt has thirteen transitive axiom audits and 259 imported project files.
`--setup` points to the exact staged objects using Lean's documented
`ModuleSetup.importArts`; shared caches were not mutated. It preserves the
required direct project imports, with no scratch sibling modules. The defining
files have hashes `1b388ffd7828390307605cc4804d7d9e1400343a3bafa0858a9d76aa0f369b33`
and `31fb27cf1e3f75a45b2ae1bfbf65625fc8784d7b6aba2f8251f9762be52ee51d`.

The earlier finite-horizon support and asymptotic support receipts remain
immutable, referenced by this receipt. Failed attempts and nonfatal tactic-style
messages remain preserved. This lane does not assert any GitHub workflow result,
all-100 compiler receipt, independent human approval or aggregate acceptance.

## 3. What changed

The previous source contained a true native envelope, source costs, arbitrary
multiplicity A6 and elementary window definitions, while the two full rate roots
were missing. The new proof composes those constructions without weakening their
domains. It establishes survival of the actual completed-input subtraction,
exact old/window memory splitting, and physical Cauchy–Schwarz before taking
limits. The original `(d+1)log(d+2)` budget is derived from the unchanged MS1
premise by a pointwise bound with the essential d=0 `log 2` correction.

There is no added simplicity assumption, global L2 premise for the undamped
prime field, attained supremum, positive-everywhere sequence premise, synthetic
field or unpriced moving source multiplier. Existing window definitions and
elementary theorem proof bodies are preserved verbatim in the staged file.

## 4. Upstream implications

The shared uniform proof compresses fixed and moving order arguments. Only an
upper asymptotic completion-normalization cost is required; the paper's stronger
separate exact limit for `log(k+1)/log T` is unnecessary. The old-memory bound
can pay a factor `T`, and window Cauchy–Schwarz can pay `C log T`: both are
subexponential. Sharp inverse-damping constants are therefore unnecessary for
these rate roots, although they may matter in future quantitative work.

The `Theta=0` case uses the matching actual upper bound and logarithmic
nonnegativity, avoiding any fictitious right-zero witness. The genuine
parameter-dependent constants are selected before each limit. This prevents
silently moving the selected zero or its multiplicity with the horizon.

## 5. Downstream implications

PROVED in the staged signatures: a hypothetical right zero of displacement
`delta>0` has `Theta≥delta`. Consequently every fixed source order, every
`C>1`, and every allowed slowly changing source schedule has the stated positive
window rate. For each `0<b<delta`, eventually

\[
 \int_{T-C\log T}^{T}|F_d|^2 > e^{2bT}-1,
\]

and likewise along every allowed moving-order schedule. The corresponding
eventual lower bound follows directly from the proved rate limit. No numerical
zero, sampling experiment or finite list of windows supplies this conclusion.

DERIVED: an independently proved cofinal zero-rate upper on the complete native
window energy forces `Theta=0`. The same applies to either complete actual
high-mask realization once its already proved norm-first rate difference is
composed with J5.2. That is the next physical consumer, not an independently
established upper bound. A small discarded contrast does not supply it.

At `Theta=0` the actual d=0 envelope is bounded on nonnegative time. Its causal
support then gives all-positive-damping L2 control of the literal original prime
field, which is the actual existing Step4 A-X interface. A conditional theorem
may consume that interface only after retaining the quiet upper as its OPEN
antecedent. It does not close RH or Step 4 unconditionally.

## 6. Resurrected routes

The fixed two-factor construction `r=2,d=1,C=2,Q=1,K=8` can now inherit `Theta`
for both full high-mask observations, rather than relying on a PAPER J5.2 input.
The source-specific quiet-observation → native-cut implication can now be
completed formally. The finite-horizon barrier remains useful when actual
quantitative coefficient estimates are available; passing a rate theorem does
not remove its positivity/vacuity thresholds at finite horizons.

No homogeneous spectral route is resurrected by these rates. The separately
audited forced-resolvent sampling identities remain compatible with nonreal
parameters and do not imply reality from positivity alone.

## 7. New RH-relevant clues and novelty assessment

The most informative remaining target is an independent upper restriction on
the complete native observation, jointly pricing its signed cancellation,
low masks and recovery cost. The rate theorem now says precisely what such an
upper would have to contradict. Uniform visibility through slowly changing
orders rules out hiding a hypothetical right zero through an unpriced source
factor within the MS1 class.

The proof uses classical mechanisms: finite-order pole/moment growth, Laguerre
orthogonality, exponential separation, Cauchy–Schwarz and elementary logarithmic
costs. Laguerre orthogonality and normalization are standard, as recorded by
[NIST DLMF 18.3](https://dlmf.nist.gov/18.3); the general complex-transform/growth
perspective belongs to the classical Tauberian literature, for example
[Korevaar's authored monograph](https://link.springer.com/book/10.1007/978-3-662-10225-1).
These references classify mechanisms, not the priority of this exact native
source/logarithmic-window statement.

The exact literal source, all-multiplicity completion, uniform moving-order
accounting and original-domain Lean composition are source-specific formal
work. The A8 mathematical argument was already present in the frozen OPICA
paper; completing its formal proof is not a new mathematical discovery or a
verified world-priority claim. It updates the earlier novelty audit's incomplete
J5.2/MS1 classification to compiled staged formalization, subject to production
replay. The earlier corpus gap remains explicit: sixteen of seventeen baseline
manuscript bodies were located; the missing moment–jet paper was citation-only.

## 8. Falsification checks

The d=0 cost control and both elementary-source zeros were checked in Lean.
Negative damping invalidates the weight-dropping argument and is excluded.
The finite-horizon barrier is exactly zero when its old-memory cost dominates.
The actual lower proof establishes the required eventual dominance rather than
reading positivity into that earlier bound.

The C=1 expected rejection verifies the original interface; it is not a
counterexample proving that a stronger C=1 theorem is mathematically false.
Dropping the slow-order premise is likewise unsupported. For instance, orders
of size `T/log T` need not satisfy MS1: their `d log(d+2)/T` cost can stay
positive. No conclusion for such a boundary schedule is asserted.

An upper bound by a positive `Theta` does not force zero rate: the auxiliary
exact control `log(1+(exp(2T)−1))/(2T)=1` compiles. This is not a synthetic
replacement for the native field. Finite quiet samples cannot establish a
cofinal quiet upper; a finite initial segment can be zero while every later
rate is one. Any future quiet estimate must address the actual complete
observation and cofinal quantifiers independently.

## 9. Highest-leverage next moves

Install the reviewed staged sources through the owner, preserve the exact
direct import contracts, replay full expected types/negative controls on the
installed bytes, and update the original-root ledger only after those gates.
Complete the two arithmetic physical consumers next, keeping quietness OPEN.
Then investigate actual signed cancellation or a source-specific upper bound;
an extra supporting theorem count is less informative than an inequality that
genuinely narrows the remaining counterexample space.

Full-100 cold compilation, parent extension, registry/dependency validation,
canonical generation, independent review and all workflow dispositions remain
separate release obligations. These proofs alone do not satisfy them.
