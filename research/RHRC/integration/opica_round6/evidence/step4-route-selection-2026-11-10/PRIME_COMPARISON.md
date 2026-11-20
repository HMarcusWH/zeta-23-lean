# Route selection: actual-prime weighted mass versus whole-slice floors

10 November 2026. Read-only comparison for the current user request. This is a research-priority judgment, not a new arithmetic theorem, compiler execution, or prediction that RH can be completed on a prescribed schedule.

## Recommendation

Choose the **fixed-source weighted-L1 response of the complete genuine Mangoldt field Z** as the primary closing target. This preserves the original divisor and echo coupling throughout the proof. A09's masked ordinary-prime field is an equivalent target at the required growth scale and a useful diagnostic. Keep the complete signed quadratic residual as a structured, stronger way to prove the target if its covariance machinery becomes useful. Do not make proving the stronger energy statement compulsory.

This choice is based on the smallest presently identified set of unpaid source/domain bridges: one original source, one actual arithmetic field, a universal exact cutoff, an eventual lower for every finite zero multiplicity, and a cofinal scalar upper. In contrast, SB/PG ask for an entire growing native slice; SG still needs an absolute arithmetic anchor and full source response control. The lower accuracy required by SB/PG is useful, but does not show that their larger domains are easier to control.

The recommendation does **not** rest on a new inequality suggesting the weighted-L1 upper is close. No such inequality was found. It is a choice of where mathematical effort is least dispersed.

## 1. The exact primary theorem

Freeze the original universal-sinc compact seed q and its literal source

`h=((D^2−1/4)q)*((D^2−1/4)q)`, with support in `[-S,S]`, `S=1/2048`.

The original seed's visibility theorem is required; an arbitrary nonnegative compact density with the same moments is not an interchangeable source.

For real `T>=16`, set

`N_T=floor(exp(T+S))`, `B_T=floor(sqrt(N_T))`,

`P_T^square(t)=sum_(B_T<p<=N_T, p prime) (log p)/sqrt(p) h(t−log p)`,

`A^square(T)=integral_0^T exp(−(T−t)/2) |P_T^square(t)| dt`.

The masked form of the single independent arithmetic supplier is:

**For every eta>0 there is C_eta>0 such that for every R>0 there is T>=max(R,16) with A^square(T)<=C_eta exp(eta T).**

Constants precede horizon choice. One upper at one fixed positive exponent is insufficient. A sequence is enough; no eventual upper at all horizons is required. The absolute value is taken **after** summing the complete signed source pulses. Taking absolute values of individual prime pulses loses their cancellation and changes the problem.

The exact A09 two-sided comparison is

`|A_Z(T)−A^square(T)| <= (1/2)||h||_infinity exp(S) T(T+S)`,

where `Z(t)=sum_n Lambda(n)/sqrt(n) h(t−log n)` contains every prime power. The recommended operational target is therefore

**For every eta>0 there is C_eta>0 such that for every R>0 there is T>=max(R,16) with `A_Z(T)=integral_0^T exp(−(T−t)/2)|Z(t)|dt <= C_eta exp(eta T)`.**

The two statements are equivalent at this every-positive-rate cofinal growth scale after absorbing the fixed polynomial and enlarging the constant. Keep Z when applying the exact divisor identity and echo equation, and use the paid transfer to the masked field when it helps. The square-root mask is a simplifying representation, not an obligation to discard the full arithmetic coupling during the proof.

Primary paper: A09; independently reviewed details: [ARITHMETIC_A07_A09B_REVIEW](../step4-new-work-review-2026-11-10/ARITHMETIC_A07_A09B_REVIEW.md).

## 2. Why that exact theorem would close the route

Let a hypothetical actual zeta zero be `rho=1/2+delta+i gamma`, `delta>0`, multiplicity `m`, and set `r=m−1`. The existing **paper-level** centered completion argument yields

`J_r A_Z(T) >= d_rho exp(delta T) − K_r ||W||_(L2(T,infinity))`,

with `d_rho>0`, `J_r=r!/(delta+1/2)^(r+1)>0`, and the actual completed output `W=a*Z` in L2. The source remains fixed independently of rho and m. No rightmost-zero or simple-zero assumption is used. The centered adjoint polynomial, not a new family of arithmetic moment channels, supplies the multiplicity handling.

A09's paid deletion then gives

`A^square(T) >= c_rho exp(delta T)` at **every** sufficiently late real T.

To contradict it, choose `eta=delta/2` in the desired upper. Fix its constant first, then enlarge R past the lower threshold and the threshold where `c_rho exp(delta T)>C_eta exp(eta T)`. The cofinal upper chooses one T beyond that R; both inequalities now concern the same T. Functional-equation symmetry and the inherited nontrivial-zero classification finish the RH implication once all source and transform hypotheses are verified.

This is the already derived paper closing logic. Its arithmetic upper is OPEN and its exact weighted consumer has not been compiled as a current Lean RH theorem. Formalization is a separate necessary delivery; current C2's all-late long-term premise must not be substituted for this cofinal weighted premise.

Sources: A08 weighted completion, original single-source archive, and [Pass18 review](../step4-study-2026-11-09/PASS18_CENTERED_JETS_AND_COMPLETE_COVARIANCE_REVIEW.md).

## 3. Paid facts, genuinely missing mathematics, and formal integration

| Component | Current role | Remaining work |
|---|---|---|
| Fixed h, moment cancellations, genuine coefficient identities | Existing source facts and paper derivations; current native coefficient interfaces also exist | Bind the exact seed/source and finite-history definitions when formalizing. No arbitrary replacement source. |
| Literal completion and centered multiplicity lower | DERIVED paper chain; reviewed, not wholly recompiled here | Audit/formalize the exact kernel transform, lower zero jets, nonzero top jet, W in L2, finite-prefix identity and terminal tail inequality. |
| Universal square-root mask | DERIVED exact finite support identity | Formalize floor/perfect-square/collar cases. All powers with bases <=B_T remain in the deleted side. |
| Deleted-base cost | DERIVED polynomial weighted-L1 bound, elementary counting | Formalize the two-sided comparison; do not relabel it as an additive energy estimate. |
| Independent cofinal every-positive-rate upper for A_Z or A^square | **OPEN core mathematical theorem** | A new source-specific estimate preserving the full signed compensation is required. Existing identities, positivity, PNT, completed-output decay and recoverability do not supply it. |
| Same-horizon contradiction | DERIVED elementary consequence | Formalize quantifier order and connect to the literal RH statement with existing zero symmetries. |

The hard work is concentrated in the arithmetic upper, but it is not a routine lemma merely because it has a short statement. The rest includes real analytic formalization obligations, rather than being a claim that only one Lean line is missing.

## 4. How the signed quadratic remains useful without overconstraining the target

Define the complete weighted energy `E^square`, exact diagonal `D^square`, and original full time-weighted singular-series model `M_h^omega` exactly as in A09. Then

`R^square=E^square−D^square−M_h^omega`.

A07/A09 independently pay the diagonal and model by fixed polynomials. Therefore a cofinal every-positive-rate upper for the residual gives one for E. Since the time-weight mass is at most two,

`(A^square(T))^2 <= 2 E^square(T)`.

Using the energy upper at rate `2 eta` gives the desired weighted-L1 upper at rate eta, after the fixed polynomial terms are absorbed. This is a valid optional proof path. The reverse implication does not follow: A09 explicitly gives a family with bounded weighted L1 and exponentially growing weighted energy.

The useful residual expansion retains every ordered distinct prime pair, the exact kernel, the source collar, and the signed model subtraction. It is not necessary to prove pointwise prime-pair asymptotics, each component small, local variance small, all-time uniformity, or an all-vector kernel inequality. Those stronger tasks should be introduced only if an actual proof mechanism requires them.

## 5. What OPICA/history contributes to the arithmetic attack

**Exact divisor/source coupling:** identities such as `Lambda=mu*log` and finite native integer/prime convolution distinguish the actual source from altered counting models. They are potential inputs to the missing inequality. Simply restating them after an invertible transformation is not an estimate.

**Completion/echo machinery:** the strong independently controlled completed output establishes the lower under a zero and paid boundary relations. It does not license coercive inversion. The previously bounded complete pairing `integral Z(a*Z)` is indefinite; the exact kernel can hide a growing mode under the hypothetical zero. No subexponential inverse norm or range membership is obtained for free.

**Vaughan decomposition:** the fixed-source Type I energy and grouped diagonal are paid; the complete distinct-product Type II covariance remains. Group equal integer products before squaring. This is a possible representation of signed compensation, not a second required theorem. Do not replace A09's cutoff by the old `floor(exp(sqrt(T)))` without proving a new adapter.

**Prime insertion:** exact same-horizon increments retain the correlation term

`||u_p||^2−||u_(p−)||^2=−2 Re<u_p,T_p u_p>−||T_pu_p||^2`.

Both signs occur in actual-source update masses. There is no monotone energy descent just from the negative square. The full signed telescope is the candidate quantity, if this representation is chosen.

**Actual block/collar falsifiers:** coherent prime and semiprime components can be exponentially large and are compensated by their full complement. The actual prime whole-line positive Gram can put exponential energy outside the observed prefix. No per-block absolute budget or omission of the terminal collar is acceptable.

**Geometric/ground constraints:** these remain valid potential extra inputs, but their current eigenray, reciprocal-input and whole-slice hypotheses do not automatically apply to the fixed h prime history. A precise source-to-state map would be a new lemma, not a permitted notation change. No such map was found in the inspected material.

Historical sources and bounded scopes: [Pass16](../step4-study-2026-11-09/PASS16_PRIMITIVE_AND_SIGNED_PRIME_ENERGY_REVIEW.md), [Pass18](../step4-study-2026-11-09/PASS18_CENTERED_JETS_AND_COMPLETE_COVARIANCE_REVIEW.md), [Drive history](../step4-study-2026-11-09/DRIVE_HISTORY.md), and [terminal collar](../step4-study-2026-11-09/PASS20_POSITIVE_SOURCE_GRAM_AND_TERMINAL_COLLAR.md).

## 6. Why not select SB/PG/SG as the primary route now?

| Route | Genuine advantage | Main unpaid burden compared with the scalar fixed-source route |
|---|---|---|
| SB | One constant floor, parity allowed to vary with aperture, only cofinal apertures; closing consumer is formal | Must establish a lower bound for **every vector** of an entire growing physical parity slice at unbounded apertures. Finite A10 positivity does not supply the unbounded law. |
| PG | Polynomial loss is allowed; powers of the quartic cutoff can be affordable; formal consumer exists | Fixed parity and all sufficiently late apertures; still an all-vector signed estimate. No current positive absolute source anchor was identified. |
| SG | Exact geometry reconstruction reduces whole-slice floor to explicit diagonal/gap/response data | The new residual-to-geometry bound is relative to the unknown actual odd bottom. A polynomial mixed-response bound alone leaves that bottom unpaid. The absolute diagonal and full response estimates remain independent arithmetic inputs. |
| Weighted-L1 prime route | One fixed actual source, scalar observable, universal mask and cofinal upper; all multiplicities handled in the paper lower | One new independent arithmetic upper plus analytic formalization of the weighted closing chain. No proposed proof mechanism is yet validated. |

The native logarithm audit further rules out an attractive SG/PG shortcut: its norm is exponentially large even on an actual legal even slice. The signed paired action may still have a favorable bound, so PG/SB remain open rather than refuted. Source: [native logarithm obstruction](../step4-study-2026-11-09/ACTUAL_NATIVE_LOGARITHM_OBSTRUCTION_15.md).

The recommendation could change if a new source-matched whole-slice signed inequality emerges from A10/SG, or if the full arithmetic coupling yields an absolute anchor. Present finite rank compression and relative identities do not yet provide that evidence.

## 7. Exact next research deliverable

Produce one proof attempt for the displayed A_Z/A^square upper, identifying at its decisive line which genuine coefficient/source identity supplies quantitative cancellation absent from the matched comparison controls. Retain the complete complement at a common horizon. If using the energy route, prove the complete signed residual upper rather than the absolute size of its parts.

Before developing a long formal build, test that decisive proposed estimate against:

1. The positive PNT-strength comparison field, with the corrected two-sided mask endpoint; it rules out positivity + PNT + source moments alone, not all genuine arithmetic.
2. The actual large prime/semiprime blocks and their complete compensating complement.
3. The bounded completed pairing with unstable inverse example; it rules out inferring input energy from output decay.
4. The correct fixed origin and same real horizon; stationary averages or individually convenient block horizons are not the target.

If the attempt stops at another exact identity or at a fixed positive exponent, record that as the remaining line. A numerical finite check does not discharge the quantifiers. No route presently has a justified promise of completion; the selected route is the cleanest focus supported by the inspected evidence.

## Reading scope for this comparison

Fully reread the A07–A09B independent review, A08 weighted-completion report66, A09 universal-cutoff report73, current review, Pass16 prime-insertion review, Pass18 centered/covariance review, and A01–A06 history review. Selected passages of the actual native logarithm obstruction and Drive history were inspected. Current SB/PG/SG signatures and source-coupling calculations are taken from the preceding exact-head review and parent/sibling source audits. No broad external literature search, numerical replay, source change or fresh formal qualification was performed.
