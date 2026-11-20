# Step 4 route decision and exact remaining proof obligations

10 November 2026. Current PR299 remains open and draft at `b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7`, tree `d0a6b1ad78523c23834eb01f57f4910a22e30d3b`. This is a research-allocation decision based on the accumulated OPICA source, proof and failure audits. No new arithmetic theorem, Lean build, CI qualification or repository change is claimed.

## Decision

**Concentrate the main mathematical effort on a cofinal subexponential weighted-L1 bound for the complete genuine Mangoldt field.** Keep the signed quadratic/covariance expansion as a possible proof technique. Keep SB/PG as the first alternative if a genuine whole-slice estimate emerges. Do not make finite-rank scaling, universal operator coercivity, every historical branch, or the stronger energy bound compulsory.

This route currently has the smallest source-matched domain and the fewest additional unproved bridges: one fixed actual source, one scalar response, and arbitrarily late upper-bound horizons. That is a reason to concentrate effort, not evidence that the hard estimate is close or a prediction of success. None of the compared routes presently has a known proof of its decisive arithmetic input.

The useful synthesis is to **work on the full source while using the simplified prime-only target as an interchangeable endpoint**. This preserves the exact divisor, integer-drive and echo identities. It avoids trying to apply those identities unchanged to a masked field for which they were not proved.

## Comparison against the other routes

| Route | Already available | New mathematical content still needed | Decision |
|---|---|---|---|
| Complete-source weighted L1 | Literal source/prime field; completion and zero-jet machinery; paper eventual lower for every finite multiplicity; paid polynomial transport to ordinary primes | Independent every-positive-rate cofinal upper on this one actual response; weighted analytic chain still needs formalization | Primary |
| Complete signed weighted covariance | Exact quadratic, polynomial diagonal and signed model, same-horizon zero lower | Complete signed residual upper, retaining all pairs and complements | A stronger sufficient tactic inside the primary route |
| Native SB constant floor | Compiled RH implication; all-late witnesses below any depth fixed in advance | One absolute constant floor on every vector of one whole parity slice at arbitrarily large apertures | First alternative; less demanding accuracy than C1 does not remove its larger domain |
| Native PG/SG polynomial floor | Compiled polynomial closure and geometry reconstruction; paper polynomial normalization/gap costs | Absolute signed diagonal anchor AND complete mixed-response control for SG, uniformly over the required growing family; formal geometry adapters | Reserve until a new source inequality pays an actual slot |
| Optimal native probe residual | Exact best-approximation Pythagoras and innovation gain; strong convergence/tightness; zero-limit consumer | Actual limiting residual vanishes, or actual relative gains are nonsummable | Clean alternate formulation, but no supplied alignment estimate |
| Selected-ground/K3/contact | Exact distinct ground/reciprocal inputs, selected quantitative gap, packet disjointness, contact identities and finite checks | An incompatible response restriction on the exact selected packet, or a complete native no-exit estimate | Do not spend the main effort finishing finite coverage without this supplier |
| Signed-measure separator | Signed heat separator and near-gap limit theorem | Genuine native measure realization, all support/self-duality conditions and one common variation budget retaining a nonzero value | More unpaid bridges; retain for a specific new construction |

References: [current closure premise map](../step4-study-2026-11-09/CURRENT_CLOSURE_PREMISE_MAP_12.md), [geometry comparison](GEOMETRY_COMPARISON.md), [prime comparison](PRIME_COMPARISON.md), [adversarial comparison](ADVERSARIAL_COMPARISON.md).

Two facts prevent overrating the geometry route. First, the actual source-residual adapter bounds the even side relative to the unknown odd bottom; two relative bounds do not anchor a shared absolute level. Second, the crude polynomial geometry gap is already adequate for PG. Making that gap sharper or another finite factorization smaller does not supply the signed arithmetic estimate.

There is also a quantifier correction: cofinal exponential-depth witnesses and all-late arbitrary *fixed* depth do not automatically give a consumer for a polynomial floor on an arbitrary cofinal subsequence. The depth cannot be chosen as a function of an aperture selected later. SB's constant-cofinal and PG's polynomial-all-late requirements must stay distinct.

## The precise target

Freeze the repository's original universal-sinc seed q, once and for all. Set

\[
S=1/2048,\qquad h=((D^2-1/4)q)*((D^2-1/4)q),
\]

and use the actual complete field

\[
Z(t)=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}h(t-\log n).
\]

The source is the literal real `actualCorrelationSource`, not an arbitrary compact function with similar moments. Its field is the literal `actualCorrelationPrimeField`; despite that name it includes all prime powers. At any finite horizon all sums have the exact support cutoff `floor(exp(T+S))`.

Define

\[
A_Z(T)=\int_0^T e^{-(T-t)/2}|Z(t)|\,dt.
\]

**The independent arithmetic theorem to prove is**

\[
\boxed{\forall\eta>0\;\exists C_\eta>0\;\forall R>0\;
\exists T\ge\max\{R,16\}:\quad A_Z(T)\le C_\eta e^{\eta T}.}
\tag{U}
\]

The absolute value is outside the complete signed source sum. Every positive rate is required, but a polynomial bound, a constant bound, an all-time bound, a bound for every source, or one common horizon sequence for all rates is not required. Constants must precede horizon selection. A fixed positive rate alone leaves possible smaller zero displacements.

The current formal source definitions and inherited drive estimates are in [ActualSourceHyperbola](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/OPICARound4/ActualSourceHyperbola.lean#L35). Source identity is an existing input; (U) is OPEN.

## Why the complete source keeps all the recent prime-only gains

The A09 paper gives

\[
N_T=\lfloor e^{T+S}\rfloor,\quad B_T=\lfloor\sqrt{N_T}\rfloor,
\quad P_T^\square(t)=\sum_{B_T<p\le N_T}\frac{\log p}{\sqrt p}h(t-\log p).
\]

All powers of bases greater than B_T, except the first power, lie beyond the exact prefix support. All remaining powers stay in the deleted-base field. For T at least 16,

\[
\left|A_Z(T)-A_{P_T^\square}(T)\right|
\le \tfrac12\|h\|_\infty e^S T(T+S).
\tag{M}
\]

Thus (U) is equivalent to its masked version at the every-positive-rate cofinal scale, by absorbing a fixed polynomial into the chosen exponential allowance. This is a reviewed paper deduction, not a new upper bound. It does not compare additive energies or license removing mixed terms from a squared norm.

The proof can therefore exploit the full relation `log = 1 * Lambda`, the exact integer action and all causal histories, then use (M) if an ordinary-prime formulation is useful. The mask does not become a new completion kernel.

## The closing contradiction is already explicit at paper level

For an actual hypothetical zero `rho=1/2+delta+i gamma`, with delta positive and finite multiplicity m, put `p=delta+i gamma` and `r=m-1`. With the exact source transforms,

\[
C(p)=\frac{p-1/2}{(p+1/2)(p+3/2)},\quad
d_\rho=|C(p)H(p)\zeta^{(m)}(\rho)|>0,
\]

\[
J_r=\frac{r!}{(\delta+1/2)^{r+1}},\qquad
K_r=\sqrt{\frac{(2r)!}{(2\delta)^{2r+1}}}.
\]

The fixed source's genuine visibility theorem is what makes H(p) nonzero; no arbitrary source replacement is allowed. The complete output W satisfies `W=a*Z=c*U` and belongs to L2. The centered weighted completion argument gives

\[
J_r A_Z(T)\ge d_\rho e^{\delta T}
-K_r\|W\|_{L^2(T,\infty)}.
\tag{L}
\]

Because the tail tends to zero, `A_Z(T) >= c_rho exp(delta T)` at every sufficiently late real T. This handles arbitrary finite multiplicity without a rightmost-zero assumption and without increasing the source's derivative order.

If (U) is proved, choose eta=delta/2, fix its constant, and enlarge R past both the threshold for (L) and the threshold where `C_eta exp(eta T) < c_rho exp(delta T)`. The horizon supplied by (U) contradicts (L) at that same T. Functional-equation symmetry then handles leftward off-line zeros.

This is a sufficient paper chain, not an already compiled unconditional RH theorem. The mathematical unknown is (U); the complete weighted formal chain also remains to be checked and implemented.

### Do not exclude legitimate conditional use of OPICA

(U) is the clean unconditional target, not an additional restriction on proof by contradiction. For each arbitrary actual hypothetical zero rho with displacement delta, it would also suffice to derive from its legitimate coupled constraints one rate `0 <= eta_rho < delta`, a constant `C_rho > 0`, and a cofinal upper `A_Z(T) <= C_rho exp(eta_rho T)`. The rate and constant may depend on rho, but must be fixed before choosing T. They then contradict the eventual lower for that same zero. Every-positive-rate control is not required in this conditional version.

This keeps the generated-packet, ground and other zero-dependent OPICA constraints available. Their use needs the exact map to Z; a ground vector is not automatically this history field. Deriving an opposing upper from the hypothetical zero and arithmetic is valid. Assuming that upper, or a zero-free conclusion strong enough to imply it, is not a derivation. Either proof form can finish the same selected response route; no separate research program is being required.

## Exactly what remains to prove or formally connect

| Obligation | Existing evidence | Required completion |
|---|---|---|
| S0: literal source and field | Current native definitions, compact support, finite history and source visibility; original single-source paper identifies h | Bind the precise real correlation source, its normalization and the genuine Lambda coefficients in the new weighted theorem |
| S1: completion and transforms for this source | Existing local finite-history completion modules; paper transport to h and transform formulas | Formalize/verify `a*Z=c*U`, `W in L2`, `A(z)=C(z) zeta(z+1/2)` and `W_hat(z)=-C(z)H(z)zeta'(z+1/2)`, paying the removable point and holomorphic domains |
| S2: weighted zero-jet lower | Reviewed centered finite-prefix argument for (L); actual polynomial moment/adjoint modules | Use finite `Z_T` in the causal L2 operator, not an assumed global L2 Z. Prove lower-jet vanishing, nonzero top jet and the actual truncated-output tail bound; retain multiplicities |
| U: independent arithmetic upper | No proof identified | Prove (U) from actual arithmetic without RH, a zero-free premise of the needed strength, a subexponential inverse assumption, or an equivalent unproved bound hidden inside a new definition |
| S3: common-horizon contradiction | Elementary paper deduction above | Fix eta and all constants before horizon selection; apply the eventual lower and cofinal upper to the same literal object; conclude Mathlib's exact RH statement |
| Optional M: prime-mask adapter | A09's finite support and polynomial weighted-L1 comparison | Formalize floor, perfect-square and support-collar cases if the proof works on the masked side; not necessary if (U) is proved directly for Z |
| Final qualification | Existing proof/claim-validation workflow | Compile the actual new chain, audit complete statements and transitive axioms, and qualify its exact committed head. Passing a conditional theorem does not discharge U |

The source-matching analytic obligations S0–S2 are substantive formal work. The table does not imply that only one short Lean lemma remains. Nor should another large infrastructure build be confused with progress on U.

## The first research object: the complete signed discrepancy action

Keep both the exact divisor/completion relation and a direct arithmetic representation available. For `E_psi(x)=psi(x)-x`, compact support and integration by parts give, for t at least S,

\[
Z(t)=e^{-t/2}\int_{-S}^{S}e^{u/2}E_\psi(e^{t-u})
\left[h'(u)+\tfrac12h(u)\right]\,du.
\tag{D}
\]

This retains every prime power and the full signed discrepancy. The continuous main vanishes by the exact half-pole moment; boundary terms vanish by compact support. The initial interval can be retained separately (in fact Z is zero before log(2)-S). Consequently the target is a quantitative bound on this *particular filtered discrepancy*, not a pointwise square-root bound for the entire prime-counting error and not a bound on each signed term separately.

The immediate research deliverable should be one new inequality for the complete action (D), or for its complete signed quadratic, that uses a genuine coefficient relation absent from the comparison controls. It must retain cancellation before absolute values, and it must yield the rates and horizons in (U). The exact divisor identity is a possible input, not itself a norm estimate.

There is no currently established sequence of elementary deductions from the available identities to (U). Calling the missing step coercivity, rigidity, compatibility or anti-resonance would not discharge it. A successful proof must supply the quantitative line and its independent reason.

## How the rest of OPICA contributes without creating unnecessary obligations

| Machinery | Use in this route | Boundary to preserve |
|---|---|---|
| Native divisor and integer-drive identities | Keep the source completely genuine; exploit relations between all prime powers and the rapidly controlled integer drive | Small completed output does not imply a small input |
| Causal echo, Laplace jets and source visibility | Already force (L), including multiplicity, with literal terminal histories | Do not claim a bounded inverse or global prime-field L2 membership |
| A07 model and A09 diagonal | If using the quadratic method, their polynomial bounds pay these terms | They bound the model/diagonal, not actual prime discrepancy |
| Complete Type I/II and insertion identities | Alternative expansions that expose signed compensation | Preserve all ordered pairs, equal-product grouping, cross terms and one common horizon |
| Shared-ground, source jets and geometry | Potential additional arithmetic information if an exact map to the chosen field is proved | Do not identify a source-normalized ground, reciprocal input, leakage normal and h-history by analogy |
| A10 finite certificate | A qualified finite representation or a diagnostic for a separately specified structural lemma | No automatic uniform scaling, innovation alignment or estimate of A_Z |
| Historical falsifiers | Reject strategies known to lose the essential information | Each control has its own preserved hypotheses; their union is not a full native countermodel |

For the optional quadratic method, let `E^square = R^square + D^square + M_h^omega` with the exact A09 definitions. A cofinal all-positive-rate upper for R, together with polynomial D and M, gives an upper for E. The inequality `(A^square)^2 <= 2 E^square` then gives (U), using the energy bound at rate 2 eta. No converse L1-to-energy implication is available. The quadratic route is useful if it reveals a proof mechanism, not a required detour.

## Stop repeating these failed inferences

- Positivity, PNT-scale information and source moments alone: a matched positive comparison density still has exponential filtered response. A proof must identify the exact arithmetic property that this control loses.
- Polynomial whole-line positive Gram: false for the actual prime input because of its exponential terminal collar. The observed prefix and full future output cannot be exchanged.
- Per-prime-block or per-semiprime-block smallness: some genuine components are exponentially large and canceled by their full complement.
- Bounded completed pairing implies an input upper: the pairing is not coercive; the hypothetical-zero diagnostic exhibits the problem explicitly.
- Another exact deconvolution, noncollision or rank identity: it is progress only if it supplies an independent estimate on the actual quantity being bounded.
- A fixed exponent improvement: it does not cover arbitrarily small positive zero displacement.

The relevant controls do not prove that the full genuine-source constraint system is insufficient. They specify what a new proof has to use and what it cannot discard.

## Completion criterion and allocation

Focus mathematical effort on U. Bring supporting machinery into that attempt when it supplies a concrete bound on the same source, norm and horizon. Keep one failure ledger stating the first unsupported inequality in each attempt. A valid new source inequality is progress; another equivalent target or finite agreement is not a closure.

Promote SB/PG immediately if an independent native absolute floor becomes available. Otherwise do not run parallel certificate-scaling, gap optimization, universal inversion and signed-measure construction programs as compulsory prerequisites.

The project closes this route when U, or a valid zero-dependent slower-rate upper described above, supplies the source-correct weighted contradiction and the exact RH theorem passes the full formal gates. That has not happened in this comparison. The completion criterion is the fully proved contradiction, not adherence to the stronger unconditional formulation when the conditional one succeeds.

## Evidence for this decision

- [Live PR identity](PR_IDENTITY.json), unchanged from the pre-focus sweep.
- [Prime-route comparison](PRIME_COMPARISON.md), [geometry-route comparison](GEOMETRY_COMPARISON.md), [independent adversarial comparison](ADVERSARIAL_COMPARISON.md).
- A08 weighted lower, A09 exact mask and residual, original single-source archive.
- [NativeCompletionEquation](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/NativeCompletionEquation.lean), [NativeCausalAdjointZeroJets](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/NativeCausalAdjointZeroJets.lean), [NativeFloorCompletionSource](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/NativeFloorCompletionSource.lean): current full source reads. The first proves completion for its named original source; its use for the different correlation source requires the literal transport described above.
- [ActualSourceHyperbola](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/OPICARound4/ActualSourceHyperbola.lean): current lines 1–210 read for source definitions, finite cutoff and drive transfer; not a fresh complete reread of the module.
- Original single-source `REPORT.tex`, SHA256 `8869c71d5f99cafe6e9700e225832d643b9169a9777d04654a6cc66ce3e5c573`: hash rechecked and lines 1–330 reread, including fixed source, transforms, centered lower and Type I/II obligations. No new external theorem or numerical replay authority is claimed.
- An independent bounded review checked the displayed discrepancy formula (D), the weighted transport, rate conversion and common-horizon contradiction without finding a concrete error. It did not reauthenticate the entire inherited analytic chain or run a compiler. Current source snapshots and their precise reading scopes are in `SOURCE_READING_RECEIPT.json`.
