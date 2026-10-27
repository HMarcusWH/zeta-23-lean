# OPICA: proof-directed deep search

**Date:** 25 October 2026  
**Repository:** `HMarcusWH/zeta-23-lean`  
**Pinned head:** `e6baabd98dc9d6c3228c168f786524604830e163`  
**Git tree:** `09bb70b30fbfeac710cf7684f95e7d142f305fe2`  
**Disposition:** Research investigation; no repository modifications or new Lean-verified claims.

## 1. Outcome

This search did not produce a complete proof of RH. It did produce a more precise map of the mathematical work still needed, an explicit countermodel ruling out an attractive family of shortcuts, and quantitative consequences of the existing OPICA first-cell theorem.

The principal findings are:

1. **The two dependency datasets are consistent on their shared mathematical records.** The obvious cross-graph contacts do not themselves discharge a closing premise. The nine direct contacts singled out by the graph reduce to five transform identities, two preservation-of-domain lemmas, and two conditional Step 4 interfaces.
2. **DERIVED — the positive-damping L2 abscissa of every fixed native source is exactly the maximal zero displacement Θ.** In the actual zeta construction, A-X, B-Y, zero displacement, and the complete quiet-observation condition are equivalent through existing results. They are different possible proof methods, not independent established upper bounds.
3. **DERIVED — positivity, causality, a strict convolution contraction, identical spectral power, and a stable completed input do not establish causal range closure.** Two explicit positive kernels have the same power spectrum and the same input Gram operator, but different causal range closures. This is a targeted falsifier of generic operator shortcuts, not a model of the complete arithmetic construction.
4. **DERIVED — fixed-witness quantifiers are enough.** A proof that fixes one hypothetical off-line zero and then sends a separate horizon to infinity does not require uniform coercivity across all zeros or all bases. The actual missing ingredient is a source-correct approximation/sign estimate for that fixed witness.
5. **DERIVED — one positive test detects the fixed imaginary direction, while four detect an arbitrary real/imaginary combination, with explicit quantitative margins extracted from the existing first-cell proof.** The qualitative four-point sign argument is already in the repository. This report supplies an explicit norm margin, a smooth positive-test realization with an error budget, and conditioning estimates. It is not a new proof that phases change sign.
6. **LEAD — the most focused next bridge is phase-sensitive and source-specific.** It must connect actual arithmetic observations to the fixed-witness detector, or to a causal adjoint witness, with an independently proved error bound. Pure autocorrelation or generic positive-Gram reasoning loses information that the countermodel shows is essential.

The terms **PROVED** in the source inventory refer to the exact existing formal statements and their available compiler evidence. Results derived in this report are labeled **DERIVED**, not Lean-proved. No Lean executable was available in this analysis environment; the new arguments below were checked mathematically, symbolically where applicable, and numerically as consistency checks.

## 2. What was actually inspected

The uploaded complete repository ZIP was used, not a reconstruction from conversation summaries. Its ZIP comment identifies the pinned commit. More importantly, its complete Git tree was independently reconstructed from raw file bytes and Unix modes, and matches the published tree exactly.

- Archive SHA-256: `718ae97f36ddf92404d887abbafed997c8cd88932678499fff294c8432caeb7c`.
- Files: 4,780.
- Reconstructed tree: `09bb70b30fbfeac710cf7684f95e7d142f305fe2`.
- Registered dependency shards: all 16 authenticated against their recorded byte sizes and SHA-256 values.
- Reconstructed registered logical stream: 112,050,770 bytes; SHA-256 `78c7ecda2299328e5dc57ad31c8d5892b65f5b8f78ed4091e5b7efd7c3061cb4`.
- No source file in the extracted repository was edited.

The structural pass covered both complete declaration datasets and all 1,775 source-only root type records. The semantic pass directly followed the nine strongest direct cross-graph matches, the 14 source-only types mentioning the terminal RH proposition, the new native rate/consumer chain, the signed-measure and first-cell construction, the actual causal completion interfaces, and selected multi-interface first-crossing/Schur routes. It is not a line-by-line proof review of all 1,353 Lean files.

The source-only surface is explicitly discovery-only. A compiler-resolved type is not a substitute for an axiom audit or an independently checked use of every candidate theorem. Full release acceptance and graph freshness were not re-certified in this research pass.

## 3. The two graph sets and the useful projection

| Population | Count |
|---|---:|
| Registered dependency declarations | 18,915 |
| Source-only dependency declarations | 16,107 |
| Shared declaration identities | 12,899 |
| Registered-graph-only identities | 6,016 |
| Source-only-graph-only identities | 3,208 |
| Old registered theorem roots | 194 |
| New OPICA theorem roots | 100 |
| Source-only theorem roots | 1,775 |
| Source-only roots contacting an existing interface | 874 |
| Source-only roots contacting multiple interfaces | 185 |
| Registered dependency entries | 1,010,103 |

For every shared declaration, its kind, defining module, local/external scope, private/internal status and complete dependency edge records agree across the datasets. Their schema/provenance/discovery-authority wrappers differ intentionally.

Edges are directed **declaration → constant used by the declaration**. A shared ancestor is not a theorem that one result implies another.

### Old versus new registered roots

The following are project-local transitive closures **including roots**, not theorem counts:

| Projection | Old 194 closure | OPICA 100 closure | Shared | OPICA-only |
|---|---:|---:|---:|---:|
| ANY type/value/structure dependency | 7,781 | 6,397 | 3,140 | 3,257 |
| Theorem-value-erased support | 1,699 | 1,590 | 871 | 719 |
| TYPE only | 480 | 398 | 64 | 334 |
| TYPE plus STRUCTURE | 827 | 691 | 346 | 345 |

The theorem-value-erased projection retains TYPE and STRUCTURE dependencies for all declarations and VALUE dependencies only for non-theorems. It removes many edges caused by the mechanics of a proof while retaining mathematical definitions. It is a useful search aid, not a semantic proof checker. Definitions can still package assumptions, and a theorem type can still be a conditional implication.

These counts were independently recomputed with explicit inclusion rules. They supersede preliminary conversation counts whose closure conventions were not fully specified.

### The nine direct contacts

Criterion: a source-only root directly depends on an old-namespace declaration reached by new OPICA roots but not by the old registered roots.

| Candidate family | Roots | Actual content | Verdict |
|---|---:|---|---|
| `DictionaryArchWeight` | 5 | Integrability and Fourier/digamma-weight identities | Useful transform adapters; no quiet upper bound |
| `NativeDampedCompletionPointwise` | 2 | Causal support and L2 preservation for an input already in the correct space | Does not establish L2 membership of the original prime field |
| `Step4OutputSufficiency` | 2 | B-Y sufficiency and the disjunction of three closing cuts | Closing premises remain explicit |

The exact names, full types, source paths, line numbers and dependency flags are in `bridge_candidates.json`.

No source-only root directly uses the new `OPICAFollowup` namespace. This is an implementation fact, not mathematical independence. Existing first-crossing results remain useful targets for new composition, but the graph does not contain an already implemented hidden connection to OPICA.

## 4. Closing-cut compression: what the new rate theorem buys

### 4.1 Existing formal statements

The fixed-source theorem in `NativeWindowRate.lean` proves, for every fixed source order d and C > 1,

\[
\lim_{T\to\infty}\frac{\log(1+E_d(T;C))}{2T}=\Theta,
\qquad
E_d(T;C)=\int_{T-C\log T}^{T}|F_d(t)|^2\,dt.
\]

Here F_d is the literal native prime field, not an arbitrary signal. The explicit-formula envelope gives a constant K_d with

\[
|F_d(t)|\le K_d e^{\Theta t}\quad(t\ge0).
\]

MS1 extends the rate identity to arbitrary cofinal real horizons and source orders with d log(d+2) = o(T). The fixed-source theorem does not require a rightmost zero or a simple-zero assumption.

`Consumers.lean` identifies the rates of both complete two-factor high observations with the same Θ. Its quiet-observation consumer retains an explicit quiet upper-law antecedent. The full audit already proves the equivalence between complete quietness and Θ = 0.

### 4.2 DERIVED: exact positive-damping abscissa

For fixed d, define

\[
I_d(\varepsilon)=\int_0^\infty e^{-2\varepsilon t}|F_d(t)|^2\,dt,
\qquad \varepsilon>0.
\]

Then:

- If ε > Θ, I_d(ε) is finite by the envelope and an elementary exponential integral.
- If 0 < ε < Θ, I_d(ε) is infinite.

For the second claim, suppose I_d(ε) is finite. For sufficiently large T the logarithmic window is contained in [0,T], so

\[
E_d(T;C)\le e^{2\varepsilon T} I_d(\varepsilon).
\]

Consequently its logarithmic rate is at most ε, contradicting the proved rate Θ. Therefore

\[
\inf\{\varepsilon>0:I_d(\varepsilon)<\infty\}=\Theta.
\]

This argument makes **no claim about the boundary ε = Θ**.

### 4.3 DERIVED: A-X and B-Y have the same truth value in this construction

The existing native-source chain is

\[
\Theta=0\Rightarrow\mathrm{A\!\! -\!\! X}
\Rightarrow\mathrm{B\!\! -\!\! Y}
\Rightarrow\mathrm{RH}.
\]

RH forces every actual nontrivial zero to have displacement zero, so the definition of Θ gives the reverse implication to Θ = 0. Thus, **within the actual zeta construction**, these propositions and the complete quiet upper law are equivalent.

This does not turn generic causal range closure into generic L2 invertibility. The converse passes through the actual zeta theorem and its source-specific results. It also does not make A-X and B-Y the same proof method: either may be easier to attack analytically. It does mean that counting the equivalent formulations as several independent restrictions would overstate progress.

### 4.4 Upstream and downstream implications

The new result removes the earlier need to assume the native rate law. It does not remove the need for an independent upper estimate.

The slow-source theorem also blocks a proposed evasion: increasing derivative order within d log(d+2) = o(T) cannot eliminate a positive exponential rate. A source-order schedule outside that regime requires a new cost analysis; the old estimate cannot be reused there.

## 5. Exact countermodel: positive twins with identical power but different causal ranges

This is an explicit derivation from this research pass. It is not claimed to be new in the literature, and it is not a counterexample to any actual-zeta theorem.

Let H = L2(0,∞), extend inputs by zero to negative times, and let

\[
f(t)=e^{-t}\mathbf1_{t\ge0},\qquad r=\frac32,\qquad c=\frac14.
\]

Define two real, positive, causal kernels

\[
a_-(t)=c\,[f(t)+r f(t-1)],\qquad
a_+(t)=c\,[r f(t)+f(t-1)].
\]

Both have mass 5/8, so convolution by either has operator norm at most 5/8, strictly below the native completion's established bound 605/621. Both are strictly positive for t ≥ 0 and obey an exponential envelope of the same elementary form a(t) ≤ exp(-t/2). They are still not the actual floor kernel.

Their Laplace transforms are

\[
A_-(z)=\frac{1+r e^{-z}}{4(z+1)},\qquad
A_+(z)=\frac{r+e^{-z}}{4(z+1)}.
\]

### 5.1 Identical spectral power and identical input Gram operators

For every real ξ,

\[
|A_-(i\xi)|^2=|A_+(i\xi)|^2
=\frac{13+12\cos\xi}{64(1+\xi^2)}.
\]

Thus their full-line power-spectrum observables coincide. By Plancherel, their causal convolution operators T_- and T_+ satisfy

\[
T_-^*T_-=T_+^*T_+.
\]

This is stronger than equality of a single norm or finitely many moments.

Nevertheless A_- has right-half-plane zeros

\[
\lambda_k=\log(3/2)+(2k+1)\pi i,
\]

whereas A_+ has none there: in Re z > 0, |exp(-z)| < 1 < r. The displacement log(3/2) is between 0 and 1/2, and k may be arbitrarily large.

The ratio

\[
B(z)=\frac{1+r e^{-z}}{r+e^{-z}}
\]

has unit boundary modulus. With w = exp(-z),

\[
|r+w|^2-|1+rw|^2=(r^2-1)(1-|w|^2).
\]

It therefore carries zero/range information invisible in the common boundary power. This is an explicit causal phase ambiguity.

### 5.2 The causal range closures really differ

Write E for convolution by f and D for the unit delay on H. Then

\[
T_+=cE(rI+D).
\]

Since ||D/r|| < 1, rI+D is boundedly invertible by its norm-convergent geometric series. E has dense range: every smooth compactly supported function y in (0,∞) is E(y'+y). Therefore T_+ has dense range.

For a zero λ of A_- with Re λ > 0, the continuous functional

\[
\ell_\lambda(y)=\int_0^\infty e^{-\lambda t}y(t)\,dt
\]

annihilates the entire range of T_- and its closure, since

\[
\ell_\lambda(T_-u)=A_-(\lambda)\ell_\lambda(u)=0.
\]

Its norm on H is (2 Re λ)^(-1/2), and it is nonzero. T_- therefore does not have dense range.

So **positive causal contractions with the same T* T can have different causal output-range closures**.

### 5.3 Stable completed input does not repair the gap

Fix λ = log(3/2) + 9πi and put X(t) = exp(λt) for t ≥ 0. X is not in H. The locally defined causal convolution Y = a_- * X is

\[
Y(t)=\begin{cases}
\dfrac{c(e^{\lambda t}-e^{-t})}{\lambda+1},&0\le t<1,\\[4pt]
-\dfrac{c(1+r e)e^{-t}}{\lambda+1},&t\ge1.
\end{cases}
\]

It is an L2 function. Yet

\[
\ell_\lambda(Y)=A_-'(\lambda)=\frac{c}{\lambda+1}\ne0.
\]

Hence

\[
\operatorname{dist}(Y,\overline{\operatorname{range}T_-})
\ge\sqrt{2\Re\lambda}\left|\frac{c}{\lambda+1}\right|
\approx0.00795249638724>0.
\]

The same construction persists after damping by ε with 0 < ε < Re λ: replace the kernel and output by exp(-εt) times themselves and the witness by λ-ε.

### 5.4 Consequence for OPICA research

This falsifies the proposed generic implication

> positive causal completion + norm below one + stable Y + pointwise a*X=Y ⇒ Y lies in the causal L2 range closure.

It also shows why a norm below one would invert **I-T**, not T itself.

It does **not** refute the actual arithmetic closure proposition. The twins do not satisfy the exact floor-kernel identity, native source identities, all admissible-word restrictions or the entire OPICA theorem inventory. Rather, they identify information that a successful source-specific proof must use beyond positivity and power-spectrum data.

The finite-dimensional forced-Gram countermodel in §9 points in the same direction: positive spectral geometry is compatible with nonreal parameters when the equation remains forced.

## 6. Quantifier correction: fix the witness before growing the horizon

The formal theorem `canonical_pair_negative_mass_budget` has the order

\[
\forall\rho\text{ off-line zero},\quad
\exists c_\rho>0,\quad\forall(a,b)\in\mathbb R^2,
\quad c_\rho\sqrt{a^2+b^2}\le N_\rho(a,b),
\]

where N is the actual off-lattice sinc-weighted Jordan negative mass.

The dependence of c_ρ on ρ is a genuine limitation for moving/colliding zeros and growing spaces. It is **not** a limitation for every contradiction argument.

### DERIVED fixed-witness contradiction criterion

Fix ρ first. Suppose an independently constructed sequence has coefficients a_T,b_T with

\[
\sqrt{a_T^2+b_T^2}\ge a_0>0,
\qquad N_\rho(a_T,b_T)\to0.
\]

Then c_ρ a_0 ≤ N_ρ(a_T,b_T) is impossible. No bound uniform in ρ is needed.

This is a modest logical observation, not a supplied closing estimate. The missing theorem is the actual source-dependent smallness of N, or a suitable finite-observation substitute. It should not be replaced by the assumption that arbitrary real and imaginary jets are independent; the repository's canonical offcritical pair is the valid basis.

## 7. DERIVED quantitative first-cell observation theorem

The repository already contains the first-cell formula and the four-point sign proof. This section extracts explicit constants and passes from point observations to positive smooth integral tests.

Take

\[
\rho=\tfrac12+\delta+i\gamma,\quad
0<\delta<\tfrac12,\quad \gamma>\frac{2\pi}{\log2},
\quad q=\delta+i\gamma,\quad\kappa=\tfrac14-q^2,\quad Z=\kappa/q.
\]

Reflection/conjugation can handle the opposite signs; the stated quantitative theorem retains these assumptions explicitly. No synthetic parameter in the computation is claimed to be a zeta zero.

For the actual first-cell density,

\[
g_\rho(e^u)=Z e^{-u/2}\sinh(qu),\qquad0<u<\log2.
\]

At u_j=jπ/(2γ), x_j=exp(u_j), j=1,2,3,4, set

\[
p_1=e^{-u_1/2}\cosh(\delta u_1),\quad
p_2=e^{-u_2/2}\sinh(\delta u_2),\quad
p_3=e^{-u_3/2}\cosh(\delta u_3),\quad
p_4=e^{-u_4/2}\sinh(\delta u_4).
\]

The four density values are exactly

\[
(iZp_1,\,-Zp_2,\,-iZp_3,\,Zp_4).
\]

All p_j are positive. Let m=min_j p_j and

\[
\eta_\rho=|Z|m/\sqrt2>0.
\]

For every c∈C,

\[
\min_j\Re(cg_\rho(x_j))\le-\eta_\rho|c|.
\]

**Proof.** Write cZ=X+iY. The four observations are -p_1Y,-p_2X,p_3Y,p_4X. One of |X|,|Y| is at least |cZ|/sqrt2; the appropriate member of its positive/negative pair gives the estimate.

### 7.1 A single test for the fixed imaginary direction

The four tests protect against an unknown phase or changing coefficient direction. If the target is specifically the imaginary part of the actual zero measure, one of the four points already suffices. Since

\[
\Im Z=-\gamma\left(1+\frac1{4(\delta^2+\gamma^2)}\right),
\]

at x_4 = exp(2π/γ),

\[
\Im g_\rho(x_4)=-m_\rho,\qquad
m_\rho=\gamma\left(1+\frac1{4(\delta^2+\gamma^2)}\right)
 e^{-\pi/\gamma}\sinh(2\pi\delta/\gamma)>0.
\]

For fixed δ>0, m_ρ tends to 2πδ as γ→∞. It vanishes at δ=0, exactly as the imaginary zero-measure direction does. This is therefore an offcritical-specific witness, unlike the negativity of the real density, which also occurs at on-line zeros.

A nonnegative unit-integral smooth bump supported sufficiently close to x_4 has a strictly negative imaginary-measure integral. Using the derivative bound below, a radius at most m_ρ/(4D_ρ), also bounded by half the distance to the endpoints, gives an integral at most -3m_ρ/4. Thus a source-correct nonnegative observation approximating this **one fixed integral** with error less than 3m_ρ/4 would already contradict the hypothetical zero.

This is a smaller target than constructing an entire positive measure, proving a uniform basis bound, or controlling every phase. No such nonnegative arithmetic approximant is constructed in this report.

### 7.2 Removing the height restriction for the fixed imaginary direction

The cycle-based point above requires γ > 2π/log 2. A smaller first-cell point removes that restriction. This derived statement applies for **every** δ>0 and γ>0, with no zero-height estimate imported.

Put R=|q|²+|κ| and

\[
u_* = \min\{\tfrac12\log2,\,R^{-1/2}\},\qquad x_*=e^{u_*}.
\]

R is positive because κ+q²=1/4. The entire series gives

\[
g_\rho(e^u)=e^{-u/2}u\left[\kappa+
\sum_{n\ge1}\frac{\kappa(1/4-\kappa)^n u^{2n}}{(2n+1)!}\right].
\]

For P_n(z)=z(1/4-z)^n, compare P_n(κ) and P_n(conj κ) along their vertical segment. The real coefficients and derivative bound yield

\[
|\Im P_n(\kappa)|\le |\Im\kappa|
\left(|q|^{2n}+n|\kappa||q|^{2n-2}\right).
\]

For 0<u≤u_*, therefore, the imaginary remainder in square brackets has magnitude at most

\[
|\Im\kappa| R u^2
\sum_{n\ge1}\frac{n(|q|^2u^2)^{n-1}}{(2n+1)!}
\le \frac{|\Im\kappa|}{2e},
\]

using |q|²u²≤1, Ru²≤1 and the exact identity

\[
\sum_{n\ge1}\frac{n}{(2n+1)!}=\frac{1}{2e}.
\]

Since Im κ = -2δγ, this proves the explicit bound

\[
\boxed{-\Im g_\rho(x_*)\ge
2\delta\gamma u_* e^{-u_*/2}\left(1-\frac1{2e}\right)=:m_*>0.}
\]

A positive unit-integral smooth bump centered at x_* and supported within radius

\[
\min\{(x_*-1)/2,(2-x_*)/2,m_*/(4D_\rho)\}
\]

has imaginary-measure integral at most -3m_*/4, by the derivative estimate below. Thus the one-test conditional closing target is available without excluding small heights. The critical-line direction still vanishes when δ=0.

**Scope warning:** this local density identity and sign estimate hold for generic parameters, not only zeta zeros. They cannot alone distinguish a zero from a nonzero parameter. Any successful nonnegative arithmetic comparison must therefore use genuinely zero-specific global information. Replacing that missing theorem by an assumption of positivity would merely relocate the original obstruction.

The additional numerical consistency pass tests 32 (δ,γ) pairs, including γ=0.1,1,3,5, as well as larger heights; it does not assert that any of those parameters is a zeta zero.

### 7.3 Smooth positive test functions with an explicit radius

On 1<x<2,

\[
|g_\rho'(x)|\le D_\rho
:=|Z|(|q|+\tfrac12)\cosh(\delta\log2).
\]

This follows by differentiating x^(-1/2) Z sinh(q log x) and using both |sinh(qu)| and |cosh(qu)| ≤ cosh(δu) for real u.

Choose

\[
r_\rho=\min\left\{\frac12\min_j(x_j-1,2-x_j),\frac{\eta_\rho}{4D_\rho}\right\}>0.
\]

For any four nonnegative smooth unit-integral bumps φ_j supported within distance r_ρ of x_j,

\[
\left|\int\phi_j(x)\Re(cg_\rho(x))dx-\Re(cg_\rho(x_j))\right|
\le\frac{\eta_\rho}{4}|c|.
\]

Consequently

\[
\min_j\int\phi_j\,d\nu_c\le-\frac{\eta_\rho}{2}|c|,
\]

where ν_c=Re(cν_ρ). The actual lattice atoms do not contribute: every bump is supported strictly inside (1,2).

### 7.4 The exact missing arithmetic bridge

Suppose, on the same actual arithmetic construction, one could produce real observations P_j(T) and c_T such that

\[
P_j(T)\ge0,\qquad
\left|P_j(T)-\int\phi_j\,d\nu_{c_T}\right|\le\varepsilon_T,
\qquad |c_T|\ge a_0>0.
\]

The detector gives

\[
\varepsilon_T\ge\eta_\rho a_0/2.
\]

Thus ε_T→0 would give a contradiction. In fact a single independently proved error smaller than η_ρ a_0/2 suffices.

This reduces a possible route to four source-correct scalar comparisons for one fixed witness. It does **not** construct P_j(T), their positivity, or their approximation. Those are the central mathematical obligations. Squaring a profile is not an automatic construction: the existing square-defect theorem explains why it changes the Fourier/gap constraints.

The earlier Stage22 note already derives a nonconstructive n+1 positive-test family on a fixed n-dimensional span. The present four-test calculation is an explicit, nonminimal construction with usable constants for the two-dimensional canonical pair. It is not a replacement for, or a novelty claim over, that note.

### 7.5 Conditioning and the critical-line control

The first two observation rows are perpendicular after a rotation. Their singular values are

\[
|Z|e^{-\pi/(4\gamma)}\cosh(\delta\pi/(2\gamma)),\quad
|Z|e^{-\pi/(2\gamma)}\sinh(\delta\pi/\gamma).
\]

For fixed δ>0 and γ→∞ they behave as γ and πδ. Hence the condition number behaves as γ/(πδ), and η_ρ tends to πδ/sqrt2. The bump radius obtained from the conservative derivative bound is of order δ/γ².

At δ=0 the imaginary direction disappears and the margin is zero. The test therefore has the right degeneracy; it does not erroneously exclude on-line zeros.

The first-cycle negative sinc mass in the weak coefficient direction c=conj(Z)/|Z| has the asymptotic

\[
\int_{e^{\pi/(2\gamma)}}^{e^{3\pi/(2\gamma)}}
\operatorname{sinc}^2(x)\,[-\Re(cg_\rho(x))]_+\,dx
\sim\frac{\delta}{\gamma^3}
\left(\frac{7\pi^3}{2}-12\pi\right).
\]

This describes that restricted interval and chosen direction, **not** the full global negative mass or its optimal basis constant.

The script tested 16 high-height positive (δ,γ) parameter cases with 200 coefficient angles per case, 32 height-free one-test cases, and three critical-line controls at 60-digit precision. These are consistency tests, not certified enclosures or assertions of off-line zeros. The inequalities above have direct analytic proofs independent of the sampling grid.

## 8. A second fixed-family reduction: the Schur target need not be global

The existing C-Schur definition quantifies over all admissible selectors, phases, cutoffs and shifts. This is a sufficient closing statement; it is not the only possible shape of a sufficient statement.

Fix one hypothetical zero ρ, choose 0<β<|Reρ-1/2|, and use the established producer to select a cofinal sequence of actual Step123 outputs. Let L_n→∞ be their actual apertures and S_n their **original-detector full-complement** Schur losses. The existing lower theorem gives

\[
S_n>\tfrac12 e^{\beta L_n}.
\]

Therefore

\[
\liminf_n\frac{\log(1+\max(S_n,0))}{L_n}\ge\beta.
\]

An independently proved upper limsup strictly below β on this same produced sequence would suffice for contradiction. Its constants may depend on the fixed ρ and β. One need not first prove the all-selectors uniform C-Schur formulation.

The operative missing estimate still concerns the original detector complement, not a selected-ground one-shell scalar.

### Why the inverse bound alone is insufficient

The repository supplies a small predecessor inverse budget. Abstractly, let P_L=e^(βL), B_L=e^(βL), D_L=0. Then ||P_L^-1||=e^(-βL), while the scalar Schur loss B_L*P_L^-1B_L-D_L equals e^(βL). A small inverse does not control a growing forcing vector.

For a prospective source estimate ||B_L y|| ≤ poly(L)e^(rL), the inverse-controlled term has rate at most 2r-β. To beat the lower rate β by this mechanism, one needs r<β and control of the direct complement term. The actual aperture/time normalization must be derived before inserting a native-field rate. This report does not silently identify that forcing exponent with Θ or with Θ/2.

This is a useful early rejection test for proposed inequalities: a proof that only reproduces the obstructed exponential rate has not closed the gap, even if all its constants are explicit.

## 9. Other routes tested or reclassified

### 9.1 Forced positive Gram and Stieltjes geometry

With A=diag(1,2), g=(1,1), κ=1+i, define h=κ(A-κI)^(-1)g. Then

\[
h=(-1+i,i),\quad N=3,\quad Q=4,\quad b=-1+2i,
\quad Q=\kappa(N+\overline b),\quad Q-N/4=13/4>0.
\]

Positive forms coexist with a nonreal parameter. This instantiates the already-known forced-model objection; it is not a model of the native zeta source.

The actual arithmetic spectral measure is |ζ(1/2+iξ)|²dξ/(2π), and its Stieltjes function has the expected imaginary sign. The actual boundary amplitude, however, is ζ(ρ)/b_ρ. Proving that this amplitude cannot vanish is not supplied by positivity of the spectral measure. The positive twin kernels in §5 sharpen this information-loss warning.

### 9.2 Weighted-mixture rigidity

The formal sharp-gap theorem for a mixer with exponential moment a>1/2 yields a scalar integer comb; zero origin mass forces zero. Actual nontrivial-zero co-Poisson measures have a gap and zero origin atom but are nonzero (including their lattice atoms). Thus a representation in that absolute mixing class cannot hold for all such zero measures. This includes on-line zeros.

A proposal that obtains the required absolute-moment representation without genuinely distinguishing off-line zeros is therefore asking for a false strengthening. The strict a>1/2 threshold and the renormalization order cannot be discarded.

### 9.3 Square repair

The actual square construction restores a sign but produces a nonzero continuous Fourier defect. The existing theorem rules out repairing it by arbitrary lattice-supported order-zero corrections with compatible tempered extension, even when an additional self-dual term is supplied. Self-dual projection fills the gap. This rules out that repair mechanism, not every nonlinear construction.

### 9.4 Compactness and normalization

CT1.3 retains a linear sinc budget while its quadratic normalization has unbounded variation on a fixed compact set. Distributional convergence cannot supply the missing measure convergence without a common variation budget. New fixed-basis coercivity does help when the basis really is fixed; it does not repair this varying-family counterexample.

### 9.5 First-crossing and Γ routes

The selected real-geometry modules reduce an even-selected/odd-good obstruction to explicit scalar corridors and Γ escape branches. Their types do not supply signs for Γ or an upper bound for the sharp radius. Other branches include odd-selected, simultaneous badness and predecessor resonance. The new OPICA results cannot be substituted into these scalar slots merely because the graphs share source-jet definitions.

The actual first-bad/exclusion criteria were also read. Several are already formal equivalences with the terminal proposition. Restating one as a new graph bottleneck is not an independent closing theorem.

## 10. External primary-source check

External material was consulted for connections, not used to replace private project sources or assert a novelty priority.

- Jean-François Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta function*, arXiv:math/0203120, published in J. Théor. Nombres Bordeaux 16 (2004), 65–94. Its primary abstract explicitly links zero systems, co-Poisson summation and Sonine spaces. This confirms that this broad connection is established background, not itself a new closing argument.
- Burnol, *A lower bound in an approximation problem involving the zeros of the Riemann zeta function*, arXiv:math/0103058, Adv. Math. 170 (2002), 56–70. Its primary abstract describes zero-based lower bounds in the Nyman–Beurling approximation formulation. This is relevant context for the adjoint/range obstruction.
- Burnol, *On an analytic estimate in the theory of the Riemann Zeta function and a Theorem of Baez-Duarte*, arXiv:math/0202166. A potentially attractive estimate for ζ(s)/ζ(s+A) is explicitly RH-conditional in the primary abstract. It is not an admissible independent closing input here.

Only the cited scope/conditionality information was used from these abstracts. The proofs of the new countermodel and quantitative reductions in this report are supplied independently above.

## 11. Highest-leverage next proof targets

These are recommendations after the executed search, not claims that the remaining hard step has been solved.

### Target A: fixed-witness, source-correct observation comparison

Freeze one actual off-line zero and its canonical real/imaginary measure pair. Use the height-free single imaginary-direction positive bump of §7.2 when that direction is accessible; use the four-test version or existing fixed-span construction when the extracted phase is unknown. Identify actual prime/completion/Schur observations P_j with proved signs and controlled comparison errors. Preserve the same original source, Fourier convention, phase and complete correction history.

**Success criterion:** obtain one error below the nonzero detection margin while the coefficient vector remains nonzero. An all-zeros uniform constant is unnecessary.

**Fast falsifiers:** the observable is quadratic where the target is linear; squaring changes Fourier duality; normalization lets the coefficient vanish; the error estimate assumes the quiet upper law; a different source is substituted; the allowed test cone is smaller than the positive-bump cone.

### Target B: one source-specific causal approximation, not generic density

For a fixed actual adjoint zero witness v with T* v=0 and <v,Y>≠0, every causal range approximation has distance at least |<v,Y>|/||v||. A source-specific independently justified upper estimate below that lower bound would close the contradiction. A generic positivity/contraction/spectral argument is excluded by §5.

**Fast falsifier:** run the proposed lemma on the positive twin kernels. A lemma using only their common properties cannot yield the desired conclusion.

### Target C: same-state preconditioned forcing on a cofinal generated family

Study the original-detector Schur forcing and direct complement term on the single cofinal family selected after fixing ρ. Do not demand an all-selectors theorem unless the proof needs it. Track the exact aperture scale before importing a field-growth estimate.

**Fast falsifier:** the exponential upper rate is at least β, or the proof silently replaces the full detector complement by a one-shell quantity.

### Target D: formalize the research controls before relying on them

The explicit twin-kernel countermodel, height-free imaginary-direction detector, quantitative four-bump detector, fixed-witness contradiction wrapper and damping-abscissa theorem are compact formalization candidates. They would compress the dependency map and prevent repeated false starts. Their formalization would not, by itself, supply the independent arithmetic bridge.

## 12. Post-green research assessment

**What became mathematically usable:** the existing OPICA source-rate, finite-span, first-cell, weighted-mixture and square-defect results can now be composed with the native completion and original-detector interfaces at one pinned source tree.

**What this search changed:** it separated graph contact from implication, compressed equivalent closing cuts, made a qualitative detector quantitative, and exhibited a strict phase/range obstruction surviving generic positivity and equal spectral power.

**Upstream:** do not overstrengthen fixed-witness quantifiers; distinguish T from I-T; retain causality and all correction terms; distinguish magnitude data from phase-sensitive information.

**Downstream:** a source-correct one-observation comparison (or four for unknown phase) or a same-family Schur upper estimate is a concrete next interface. The new derived results make the required precision explicit.

**Resurrected routes:** fixed finite-dimensional separation is worth revisiting because the witness can be frozen. Native-rate-dependent routes now have their rate premise proved. Generic inverse, square/lattice-only repair, uncontrolled measure limits and scalar forced-Gram exclusions remain blocked.

**Workflow evidence:** this investigation did not claim a complete final-head workflow harvest. It used the source-identical published checkpoint and the available scoped formal evidence. No unfinished release gate was counted as a passed theorem or new research result.

**Bottom line:** the strongest surviving direction is not “find another positive matrix.” It is to extract a phase-sensitive, actual-source estimate that defeats one fixed witnessed obstruction. This report isolates that obligation; it does not pretend to discharge it.

## 13. Reproduction and source index

Run on the supplied repository checkout:

```bash
python graph_audit.py /path/to/zeta-23-lean --out ./results
python mathematical_tests.py
```

`graph_audit.py` uses only Python's standard library. `mathematical_tests.py` requires SymPy and mpmath. Numerical checks use 60 decimal digits and are not interval certificates.

Artifacts:

- `provenance.json`: archive hash and complete reconstructed Git tree.
- `graph_audit.json`: exact populations, authenticated registered shards and closure projections.
- `source_only_inventory.csv`: all 1,775 exact source-only type records and interface tags.
- `bridge_candidates.json`: all nine direct cross-graph candidates with exact type text.
- `multi_interface_candidates.json`: 185 multi-interface candidates with exact type text.
- `rh_interfaces.json`: 14 source-only conditional/equivalence terminal interfaces.
- `mathematical_tests.py` and `.json`: symbolic identities and high-precision consistency checks.
- `source_index.json`: hashes and statement locations of the principal inspected sources.
- `research_ledger.json`: candidate dispositions and missing premises.

All repository references below use the pinned commit, not a moving branch:

- `Zeta23/OPICAFollowup/NativeWindowRate.lean`: `native_fixed_source_window_rate`.
- `Zeta23/OPICAFollowup/MovingSourceWindowRate.lean`: `native_slow_source_window_rate`.
- `Zeta23/OPICAFollowup/NativeExplicitFormula.lean`: Θ definition, bounds and field envelope.
- `Zeta23/OPICAFollowup/Consumers.lean`: complete mask rates and quiet upper consumer.
- `Zeta23/OPICAFollowup/Validation.lean`: quiet upper equivalence and full-domain consumers.
- `Zeta23/ExceptionalZero/NativeAnalyticOutputSufficiency.lean`: A-X, B-Y definitions and implications.
- `Zeta23/ExceptionalZero/Step4OutputSufficiency.lean`: three exact conditional closing interfaces.
- `Zeta23/CCM/NativePositiveCompletion.lean` and `NativeDampedCompletionOperator.lean`: actual positive kernel and contraction; not invertibility.
- `Zeta23/OPICAFollowup/JointObservation.lean`: complete recovery and exact norm/noise statements.
- `Zeta23/OPICAFollowup/FiniteSpanSeparation.lean`: actual fixed-basis and canonical pair coercivity.
- `Zeta23/OPICAFollowup/RenormalizedCoPoisson.lean`: first-cell formula and qualitative four-point sign theorem.
- `Zeta23/OPICAFollowup/CoPoissonJets.lean` and `ConfluentProfiles.lean`: actual normalized jets, first-cell bridge and independence.
- `Zeta23/OPICAFollowup/WeightedSpectralMeasure.lean`, `NativeResolvent.lean`, `BoundaryAmplitude.lean`: power-spectrum, forced resolvent and boundary amplitude distinctions.
- `Zeta23/OPICAFollowup/WeightedMixing.lean`, `SquareDefect.lean`, `NearGapLimits.lean`: the corresponding no-go/domain controls.
- `Zeta23/CCM/OriginalDetectorSchurLoss.lean`, `Step123NativeResidualOutput.lean`: full complement and inverse budget.
- `Zeta23/ExceptionalZero/GeneratedFamilyFinalGateEquivalence.lean`: explicit closing equivalences.
- Stage22 `DERIVED_FINITE_POSITIVE_TEST_OBSERVABILITY_2026-10-24.md` and addendum: the earlier n+1 positive-test derivation and its boundaries.
