# Fixed mathematical proof recipes for the remaining implementation

**Authority boundary:** the cited reuse declarations are in the downloaded exact-tree compiler catalogue. The new lemmas below are proposed mathematical compositions, not separately compiled by this audit. A coding repair may change elaboration tactics; it may not change the formulas, source, hypotheses, quantifiers or branch coverage. An unexpected mathematical failure is a STOP with a precise counterexample/obligation, not permission to improvise a replacement source.

Use `evidence/DECLARATIONS_BY_MODULE.md` for exact current Lean types and `API_CROSSWALK.json` for names. All current links are pinned to `efa6ceea7bba2b34ff453a70a32a0800fee98b82`.

## R1. Actual physical input Y: the missing range-obstruction composition

### R1.1 Fixed notation

Let rho be an actual `zetaZeroConfig.carrier` zero with Re(rho)≠1/2. Reuse the existing right-side reflection rhoR. Put m=zeroMult(rhoR)=zeroMult(rho)≥1,

- p=rhoR−1/2;
- epsilon=(Re rhoR−1/2)/2>0;
- w=p−epsilon, Re w>0;
- k=m−1;
- J(p)=`nativeOriginalSourceLaplace p`;
- R(p)=(p−1/2)/((p+1/2)(p+3/2));
- A_epsilon=`nativeDampedCompletionCausalL2Operator epsilon`;
- Y_epsilon=`nativeCompletedInputCausalL2 epsilon`;
- psi=`nativeCausalExponentialWitness w hw k`.

The time representative of psi is 1_[0,infinity)(t) t^k exp(−conj(w)t), so the conjugate-linear first slot of the Hilbert pairing evaluates the Laplace moment at w, and damping moves it to p=w+epsilon. Do not put conj(p) or p−epsilon into the physical input transform.

### R1.2 Reused checked declarations

- `nativeCausalExponentialWitness_inner_eq_laplaceMoment`.
- `nativeCausalExponentialWitness_inner_completedInput`.
- `nativeCompletedInput_complexLaplace` (Re p>0, p≠1/2).
- `nativeActualKernelLaplace_order_of_zero`.
- `nativeZeroJetInputMultiplier_order` and `nativeZeroJetInputMultiplier_jet`.
- `nativeZeroJetSourceFactor_ne_zero`.
- `nativeCausalLaplaceMoment_iteratedDeriv` and `_ne_zero_at_analyticOrder`.
- `nativeCompletedInput_not_mem_rangeClosure_of_analyticOrders` or its moment version.
- Existing right-side zero, damping, parameter and multiplicity lemmas.

The analytic expression is `nativeZeroJetInputMultiplier p = -(R(p)*J(p))*deriv riemannZeta (p+1/2)`. The physical transform is printed with reordered factors `R(p)*(-deriv riemannZeta ...)*J(p)`; normalize by commutative-ring algebra, not by changing J.

### R1.3 First exact lemma: the zeroth physical moment

For epsilon≥0 and Re z>0 prove

`nativeCausalLaplaceMoment z 0 (nativeCompletedInputCausalL2 epsilon) = ∫ exp(-(z+epsilon)t) Y(t) dt`.

Proof: both sides are equal to `inner (nativeCausalExponentialWitness z hz 0) Y_epsilon` by the two checked inner-product lemmas. Use `pow_zero`, `one_mul`. This avoids a second ad hoc choice of an L2 representative.

If Re(z+epsilon)>0 and z+epsilon≠1/2, substitute the checked actual Y transform and reorder factors. Thus near w:

`F_Y(z) = nativeZeroJetInputMultiplier (z+epsilon)`.

To obtain a genuine neighborhood equality, intersect the neighborhoods `0<Re z`, `0<Re(z+epsilon)` and `z+epsilon≠1/2`. Each is open and contains w. The last condition follows from rhoR≠1, an actual zero-carrier fact. Equality at a single point is not enough for an analytic-order proof.

### R1.4 Transfer the order

Apply `analyticOrderAt_congr` to the eventual equality. Apply the existing `analyticOrderAt_comp_of_deriv_ne_zero` to the translation z↦z+epsilon; it is analytic and its derivative is one. Substitute w+epsilon=p and `nativeZeroJetInputMultiplier_order rhoR hoffR`. Conclude ord_w F_Y=m−1.

Independently instantiate `nativeActualKernelLaplace_order_of_zero epsilon hepsilon rhoR w hw hshift` to obtain kernel order m. Do not derive this from the desired range conclusion.

### R1.5 Nonzero moment and exact value

The checked moment/derivative identity gives

`F_Y^(k)(w)=(-1)^k <psi,Y_epsilon>`.

Translation has derivative one at every order, so the existing input jet gives

`F_Y^(m−1)(w)=−R(p)J(p) zeta^(m)(rhoR)`.

Multiplying by (-1)^(m−1) yields

`<psi,Y_epsilon>=(-1)^m R(p)J(p) zeta^(m)(rhoR) != 0`.

There is no extra factorial: `zeta^(m)` denotes the iterated derivative, not the normalized Taylor coefficient. The order lemma handles arbitrary m, including m=1 with k=0. Prove m−1+1=m using m≥1 rather than simplifying natural subtraction without its premise.

Export the explicit value theorem and the requested nonzero theorem. The nonzero theorem can alternatively consume the actual order m−1 and the checked moment-nonzero lemma, but the explicit value is needed to audit sign, source and multiplicity.

### R1.6 Actual range nonmembership

Apply `nativeCompletedInput_not_mem_rangeClosure_of_analyticOrders` with k=m−1, the kernel order m and input order k. Alternatively use the actual annihilator plus its nonzero pairing, extending annihilation to the closure by continuity. These are two proofs of the same conclusion, not independent native constraints.

Final actual theorem takes rho and off-line status only; epsilon, w, m, psi and all order/visibility facts are constructed. It must not take `hKernelOrder`, `hYJet` or `hNotRange` as an unexplained caller premise.

### R1.7 Useful finite-iteration corollary

For the already defined residual iteration e_(n+1)=(I−A A*)e_n, e0=Y_epsilon, the actual psi lies in ker A*. Hence `<psi,e_n>=<psi,Y_epsilon>` for every n. Cauchy–Schwarz gives

`||e_n|| >= |<psi,Y_epsilon>| / ||psi|| > 0`.

Prove psi≠0 from its nonzero pairing before dividing. No strong-convergence theorem is needed. This is a conditional obstruction under an off-line zero, not a proof that the residual is zero.

## R2. Source scaling and the exact pole-killed L2 norm

The physical density has scale s>0. Start from the literal product factor equality Q_s(z)=Q_1(sz), prove it pointwise with the existing infinite-product definition, then use the actual Fourier inversion/density identification and x↦x/s change of variable to obtain q_s(x)=s^(-1)q_1(x/s).

Differentiate this exact function equality. By induction,

`q_s^(r)(x)=s^(-(r+1)) q_1^(r)(x/s)`.

The functions and derivatives are real, smooth and compactly supported. The full-line L2 change of variables gives

`||q_s^(r)||₂²=s^(-(2r+1))||q_1^(r)||₂²`.

Integrate `(q_1 q_1')'=q_1 q_1''+(q_1')²`; the compact-support boundary term is zero. Thus `∫q_1 q_1''=−||q_1'||₂²`. Expand the real square of `q_s''−q_s/4`. Its cross term is `−(1/2)∫q_s q_s''`, which becomes `+(1/2)||q_s'||₂²`. Substitute the scale formulas. This proves the original three-term norm formula with no zeta premise.

Fixed-source constants from the existing moment/derivative bounds remain theorem-defined. Numerical values of an existential eventual threshold are not needed in a classical mathematical packet. Native numerical evaluation must not claim it has evaluated such a threshold without a separate computable bound.

## R3. Finite normalization, concrete native-form error and phase quotient

### R3.1 Normalize before instantiating the large term

Let `Phi(v)=localizedFiniteVector L K v`; hL is a hypothesis for isometry/norm theorems, not an argument of this definition. Prove `Phi(c • v)=c • Phi(v)` by `Finset.sum_smul`/pointwise algebra on the existing modes and indicator. Work with a generic v of explicitly declared index `Fin (2*K+1)`; do not unfold the large padded coefficient expression.

For v≠0, `Phi((||v||⁻¹:ℂ)•v)=||v||⁻¹ Phi(v)`. Apply the existing physical-mass/Euclidean-norm identity. This gives the exact physical normalized function of the existing native unit coefficient vector. The old candidate's stuck metavariables are elaboration problems, not missing mathematical normalization factors.

### R3.2 Concrete native-form rate

Let E(L) be the already proved nonnegative normalized-native-form error budget. Existing theorem:

`E(L) exp(c0 sqrt(N/L)+beta L) -> 0` for every real beta, with c0>0 fixed by s0.

At beta=0 choose a source-only B so E(L)≤exp(−c0 sqrt(N/L)) beyond B. Combine with the actual error inequality beyond its common mass/control threshold. Set L0=max(4,B,Lmass,...), C=1, c=c0. Since for L≥4,

`1≤(1+L)L^(17/2)exp(L/2)`,

the exact displayed requested rate follows. The source normalization and the definition of N=ceil(L^4)−4 stay unchanged. Do not introduce an extra beta/rho-dependent constant.

### R3.3 Real phase quotient

For actual left/right coefficient vectors l,r=Jl, J an isometric involution, G_ij=<b_i,b_j> and E_ij=<M b_i,b_j>. Existing circulancy gives diagonal equality and off-diagonal equality. Hermitian symmetry then forces the off-diagonal values to be real. Let ν,ω,d,c be their real parts.

Expand all four terms: ||l+σr||²=2(ν+σω), energy=2(d+σc), σ²=1. Phase nonvanishing gives strict positive denominator. Cancel the factor two using its nonzero proof. Both phases are nonzero beyond the same source-only threshold; their deep excursions remain separately timed.

### R3.4 Odd cancellation

Use equality of padded and unpadded odd primitives; apply the literal constant-coefficient P, then uniqueness of finite Fourier coefficients under the exact normalized modes. This proves identical odd coefficient vectors and identical normalization. Do not infer this from a numerically small padding term or claim that the even image is unchanged.

## R4. Branches, nullities, shifts and residual semantics

### R4.1 Missing geometric facades

Use the actual inherited coefficient metric and actual pole profiles. Reexport the two physical exponential-moment iff theorems and both finrank K−2 results under L>0,K≥3. An empty carrier is a separate case, never an arbitrary default minimum.

For the exact correction use the already constructed normal coefficient and projected cubic vector. Do not use the uncorrected legal source on a neutral compression. The facade theorem must follow from `canonicalPoleNeutralRankOneIntertwining`, not assume the rank-one equation.

### R4.2 Eigenvalue iff and determinant facades

For λ below the odd neutral bottom, the existing invertible shifted odd operator supplies xλ. Forward direction is the checked eigenvector/ray theorem. Reverse direction: if S0(xλ)=1, use `D0(A0−λI)xλ=g0(1−S0(xλ))`, equivalently `(A0−λI)xλ=D0⁻¹g0·(1−S0(xλ))`, obtained from `(B0−λI)D0−D0(A0−λI)=g0S0` and `(B0−λI)D0xλ=g0`, and prove xλ≠0 using the nonzero source value. The existing determinant quotient is the requested determinant equality after multiplying by the nonzero odd determinant, or use its direct equality form if already exported.

For λ below the even bottom, use `yλ=−(D0*)⁻¹(A0−λI)⁻¹S0*`. Do not replace D0* with D0⁻¹. Prove the corresponding cubic normalization and eigenvalue iff by the adjoint identity. The sign is negative.

At a tie retain kernel projection and range membership for EVERY relevant eigenvector. For an even u, `(B0-lambda)D0u=g0 S0(u)`; for an odd w, `(A0-lambda)D0* w=−S0* <g0,w>`. Project each equation onto the opposite shifted kernel. Construct the inverse only on its positive complement and retain the actual kernel component. Instantiate this on the stored selected ground; an existence theorem choosing another even ground is not an identity for a stored odd ground. The selected even source moment M4 is nonzero when the independently constructed eigenspace is simple; S0 need not be nonzero.

### R4.3 Residuals

For a unit original neutral trial p in its own parity, T=T_sigma,0 is symmetric, lambda_p=Re<p,Tp> and r=Tp−lambda_p p. Prove Im<p,Tp>=0, r⊥p and

`||r||²=Re<p,T²p>−lambda_p²`.

The existing channel decomposition sums actual signed pole, Archimedean, prime and scalar components after the same neutral compression. Let r_i be the channel contribution after its own scalar projection. Then r=sum r_i and `||r||²=Re sum_ij <r_i,r_j>`. Preserve all complex off-diagonal pairings.

Do not apply the even M4 residual theorem to an odd input. Do not apply the selected even ground's M4≠0 to p, which has extra zero moments. The strict residual bound uses the measured/proved gap μ_odd−lambda_p, not the original negative depth D.

## R5. Exact original-source forcing

### R5.1 Native operators

Write `paperFT f(z)=∫f(x)exp(i z x)dx`. For compact C4 f define

`Arch(f)(x)=(1/(2π))∫ paperFT f(ξ) gammaBracket(ξ) exp(−iξx)dξ`,

`Pole(f)(x)=exp(x/2)∫exp(−t/2)f(t)dt + exp(−x/2)∫exp(t/2)f(t)dt`,

`Prime(f)(x)=sum_(n≥2) Lambda(n)/sqrt(n) [f(x−log n)+f(x+log n)]`,

`Response(f)=Arch(f)+Pole(f)−Prime(f)`.

Here `zetaW` means exactly `Zeta23.zetaZeroConfig.W`, and `gammaBracket` is exactly `Zeta23.EF.gammaBracket`. Import the existing mixed bridge from `Zeta23.ExceptionalZero.WeilLiteratureBridge`; do not assume a generic `EF_lit` hypothesis. Define ||f||H1 using the current `originalDetectorPhysicalH1Error f 0` (square root of the sum of the two squared full-line L2 integrals).

Use the repository's exact `gammaBracket` and coefficients. Do not introduce a factor-two symmetrization or change the repaired canonical scalar normalization. For compact support, the prime sum is uniformly finite on each bounded x interval. One common bound on n is chosen before differentiating or integrating over that interval.

C4 compact support supplies Fourier decay sufficient for integrability of gammaBracket*paperFT f and its L2 membership. At ξ=0 use an L1 bound instead of dividing by ξ. Away from zero, integrate by parts four times; every boundary term vanishes for the global hard-C4 finite image. The native gamma-bracket growth theorem supplies at most logarithmic growth. No RH assertion is used.

For compact C2 v, Fubini and the existing explicit formula give

`zetaW(f,v)=∫ Response(f)(x)conj(v(x))dx`.

The complex-linear first argument on the left corresponds to the conjugate-linear second-source convention `inner v Response(f)` on the right. Validate the mixed canonical equality at this orientation; self-quadratic values alone cannot reveal a conjugation error.

A permissible independent mixed-dictionary proof uses the exact quadratic identity and the polarization formula for a form linear in its first slot:

`B(u,v)=1/4 [Q(u+v)−Q(u−v)+iQ(u+i v)−iQ(u−i v)]`.

### R5.2 Bilinear norm bound

Obtain Cpsi>0 from the existing `Zeta23.WeilEF.digamma_growth_strip` in `Zeta23/WeilEF/VerticalLine.lean`. Evaluate at 1/4+iξ/2 and choose `C_A=8*Cpsi+|log pi|+1`; use log(2+|ξ|/2)≤2+|ξ|/2 and |ξ|≤1+ξ². This supplies the actual bound `|EF.gammaBracket ξ|≤C_A(1+ξ²)` with a constructed constant.

For f,v supported in one interval of length L, Plancherel and that bound give the Archimedean contribution at most C_A||f||H1||v||H1. Absorb the repository's Fourier normalization into the once-proved C_A.

Each elementary exponential functional is bounded by Cauchy–Schwarz. The pair of pole contributions is at most `2L exp(L/2)||f||₂||v||₂` (a conservative common-interval bound).

The two prime shifts are bounded by `2M(L)||f||₂||v||₂`, where

`M(L)=sum_(2≤n≤exp L) Lambda(n)/sqrt(n) ≤ 2(1+L)exp(L/2)`.

Use Lambda(n)≤log n, log n≤L on the finite range, and sum n^(-1/2)≤2sqrt(N), with small-N cases separate. Thus choose one theorem-constructed C_Q≥C_A+6 to obtain

`|zetaW(f,v)|≤C_Q(1+L)exp(L/2)||f||H1||v||H1`.

This is a valid large finite-aperture bound. It is intentionally not advertised as the missing subexponential arithmetic theorem.

### R5.3 Four histories of the original physical trial

Set s=s0, c=1+s, n_k=∫|k|², κ=(2n_k)^(-1/2), L=2a+2c. Original unit trial:

`f_sigma,a(x)=κ[k(x−c)+σ k(L−x−c)]`.

Let F_k=Pi*k, X=Pi*(Pk)=Pi*j. Then

`Prime(f)(x)=κ[F_k(x−c)+F_k(c−x)+σF_k(L−x−c)+σF_k(x+c−L)]`.

All four arguments are fixed. Native source causality can simplify individual terms only on the domain where the argument is negative. No global reflected term is discarded. k is even; both original lobes are exactly pole-neutral, so Pole(f)=0. The Archimedean response is the same literal two-lobe transform, not a prime-only approximation.

### R5.4 Local P transfer and compact duality

Local finiteness proves `P F_k=X`. For any supported neutral test v, the constructed compact inverse g=P⁻¹v has the same support, clamped value/first derivative and ||g||₂≤4||v||₂. Integrate by parts on the actual support interval, retaining both endpoint traces, to obtain

`<v, F_k composed with each translation/reflection> = <g, X composed with that same translation/reflection>`.

P commutes with translations and reflections because it has only a second derivative and scalar term. Native fields are locally C2, which is sufficient on this compact interval. Global X∈L2 is not needed.

For a unit finite test supported in [0,L], each translated/reflected X argument belongs to [−L,L]; native causality reduces its local L2 norm to X on [0,L]. The four terms and ||g||≤4 give the projected prime bound `16κ ||X||L2[0,L] = 8sqrt(2/n_k)||X||L2[0,L]`. Keep the actual support endpoints when a sharper bound is used.

### R5.5 Same-source convolution bridge

Since k=Pq, j=Pk, constant-coefficient differentiation commutes with compact convolution. Therefore `k*k=q*j`. The native locally finite Pi action commutes with convolution by q on every fixed compact horizon, proving `Pi*(k*k)=q*X` pointwise. This one-way smoothing identity does not license bounded deconvolution by q.

### R5.6 Exact finite projected forcing and error

Let p be the literal finite unit trial; let S be the actual predecessor at K_eta−1, J its isometric inclusion into the detector carrier, and Φ_S its physical realization. Denote x=J* p and y=(I−JJ*)p. With T the actual detector operator,

`b_eta=Φ_S*(1_[0,L](Response(p_phys)+eta*p_phys))=(P+eta I)x+B y`.

Keep b_eta as a directly constructed projected native response; equality to the spectral expression is a theorem. Using the existing Schur construction,

`Q(p)+eta ||p||²=<b_eta,(P+eta I)^(-1)b_eta>+<S_eta y,y>`.

The ground equation is separate and uses λ and its one-dimensional shell. This formula uses the whole Kd−K_eta+1 complement.

For e=p_phys−f_original, duality with unit v∈S and the bilinear bound gives

`||b_eta−Φ_S*(Response(f_original)+eta*f_original)||`

`≤ [C_Q(1+L)exp(L/2)sqrt(1+(2π(K_eta−1)/L)^2)+eta] ||e||H1`.

If S is the zero space, both sides' projected differences are exactly zero; do not ask for its lowest eigenvalue. The bound remains true.

A native selected detector satisfies eta<D/2≤−Q(p)/2≤|Q(p)|/2. The bilinear estimate and Kd finite-mode bound therefore give

`eta≤(C_Q/2)(1+L)exp(L/2)[1+(2πKd/L)^2]`.

Use this established eta control when combining the forcing error with the quartic stretched-exponential approximation. Do not silently claim an eta-uniform asymptotic for arbitrary unbounded eta.

### R5.7 Ambient, normal and outer components

For the selected finite state u, retain separately:

- Φ_legal* Response(Φu), the fixed legal projection;
- its pole-normal component removed by neutral compression;
- the neutral eigenvalue equation at actual λ;
- `(I−Φ_legal Φ_legal*)1_[0,L]Response(Φu)`, the outer Galerkin residual.

The normal term is not an exterior residual. Neither is zero merely because the neutral compression has an eigenvector. Norm/error estimates for the original trial do not attach automatically to selected u.

## R6. Original source exterior and causal history

Let R=Response(f_original). Define its interior on [0,L], left tail R(−t), right tail R(L+t), with t≥0 causal indicators. Choose endpoint ownership once (for example interior on [0,L], tails for t>0) or state the reconstruction a.e. Use the same convention in the output serializer.

These tails are NOT asserted to be L2 at every damping. They are actual locally defined functions, with transform/domain statements only when separately justified. The stable Y belongs to the existing causal L2 space independently; do not transfer that membership to the raw exterior.

For a compact probe psi supported in [−b,b], right-side convolution at x=L−b+s splits at u=s after the substitution u=b−y. The exterior contribution uses u≤s; the remaining integral uses actual R on the interior. Retain that history as an explicit finite integral. If an unrestricted or constrained contact is used in a later optional program, it needs its own producer; the original trial's interior cannot be overwritten by zero or an exponential-polynomial normal merely by terminology.

M21's original record can consume this general exact splitting without importing C05's full continuous-contact theorem. Every field is constructed from f_original, not supplied as an arbitrary response function.

## R7. Conditional terminal wrappers

### A-X and B-Y

Define the two predicates on the literal native source and causal L2 operator. The existing theorem `nativeCompletedInput_mem_rangeClosure_of_prime_memLp` proves A-X→B-Y for every positive epsilon. T01 proves nonmembership at the constructed epsilon for an actual off-line zero. Contradict B-Y.

To export Mathlib's `RiemannHypothesis`, use the repository's exact adapter from the Mathlib nontrivial-zero hypotheses to `IsNontrivialZero` and then to `zetaZeroConfig.carrier`. Do not strengthen the target to a differently defined set of zeros or assume a zero belongs to the strip without the existing adapter.

The original integral A-X formulation and MemLp version are equivalent here because the field is causal, measurable and the exponent is exactly two. Export the equivalence; do not silently alter the statement.

### C-Schur

Choose any actual off-line zero rho and beta=|Re rho−1/2|/2>0. The C-Schur premise at epsilon=beta/2 gives C>0,L0. Choose the producer's lateness R greater than 4, L0, all source thresholds and `log(2C)/(beta−epsilon)+1` (use a max to handle negative logs). Generate the chosen phase (one suffices for contradiction; full API retains both).

The existing state proves loss>D/2=exp(beta L)/2. C-Schur proves loss≤Cexp(epsilon L). The chosen L makes Cexp(epsilon L)<exp(beta L)/2. Contradiction.

This uses the complete signed Schur value. It does not bound the response term alone, infer a parity gap from depth, or invoke A-X/B-Y. Export the three wrappers with their respective explicit OPEN premise and no hidden Step 1–3 bridge.

## R8. What the agent must not infer

Positive forward mass <1 is not stable inversion. A nonzero actual adjoint pairing under an off-line zero is an obstruction, not proof that the pairing vanishes. A decreasing residual norm need not tend to zero. A finite probe grid is not the theorem's quartic family. A source-root budget conditional on a supplied divisor does not construct that divisor. A full finite D2 certificate does not inhabit Lean hWindows. A compiled conditional RH wrapper is not an unconditional proof of RH.

## R2.2. Full fixed-rate rapid integer-drive bound (T08)

This recipe supplies the required stronger public `rapid_bound`. The current first-order decay already proves the stable-input facts; it is not renamed to imply arbitrary rates.

For fixed t let `F_t(x)=x^(-1/2) log(x) j(t−log x)` on x>0, extended by zero otherwise. It is smooth and supported in `[exp(t−s0),exp(t+s0)]`, separated from zero. Its integer sum is exactly the original U(t), including the n=1 zero coefficient. Change variable u=t−log x. The continuum integral is zero because both `∫exp(−u/2)j(u)du` and `∫u exp(−u/2)j(u)du` vanish. These are the independently proved elementary zeroth/first moments of j=P²q.

Construct bounded 1-periodic functions K_N as follows. K_1(x)={x}−1/2 away from integers (integer values are irrelevant to the integral). K_(N+1) is the unique periodic primitive of K_N with zero mean. Build it on [0,1], subtract its average, then extend periodically. For N>=2 it is continuous at integer seams. Its finite bound is the maximum of its continuous unit-cell polynomial/primitive; for N=1 use1/2. No unproved Bernoulli-number estimate or new library module is needed.

For any smooth compact g whose support lies in (0,infinity), first prove the cellwise summation formula by integration by parts on integer intervals:

`sum_(n in Z) g(n) − ∫g = ∫ K_1(x)g'(x)dx`.

Only finitely many cells contribute. Iterate integration by parts, paying the matched periodic endpoint values at every integer, to obtain for N>=1:

`sum g(n) − ∫g = (-1)^(N+1)∫ K_N(x)g^(N)(x)dx`.

For F_t, use the exact derivative recurrence

`F_t^(N)(x)=x^(-N-1/2)[log(x) A_N(t−log x)+B_N(t−log x)]`,

`A_0=j, B_0=0`,

`A_(N+1)=−(N+1/2)A_N−A_N'`,

`B_(N+1)=A_N−(N+1/2)B_N−B_N'`.

A_N and B_N are explicit finite linear combinations of derivatives of the actual j, supported in [−s0,s0]. Changing variables gives a source-only C_N such that for t>=max(s0,0):

`|U(t)| <= C_N(1+t+s0) exp(−(N−1/2)t)`.

Given A>0, choose the integer N=ceil(A+2). Then d=N−1/2−A>0. Since `t exp(−d t)<=1/d` for t>=0 and `exp(−d t)<=1`, choose `C=C_N(1+s0+1/d)+1` and T=max(s0,0). This proves

`∀ A>0, ∃ C>0,T>=0, ∀t>=T, |U(t)|<=C exp(−A t)`.

The construction is source-only after A is specified; it requires no zero, inverse or actual X norm bound. The proof does not claim the optimized `exp(−k exp(t/2))` bound, which would additionally optimize N against the Gevrey derivative constants. That stronger A03 use remains outside core.
