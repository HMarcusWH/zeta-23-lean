# Preserved written proof sources

These are inherited paper arguments, not compiler receipts. Their unchanged individual inputs and hashes are recorded in SOURCE_REGISTER.json. Adopt their exact scope and all versioned audit clarifications.


---

## Source: ROUND2_RESEARCH.md

# OPICA Round 2: source-preserving probe, exact Gram problem, and certified exclusion contracts

**Research continuation — 25 October 2026**

## Result and authority

This pass did not establish the terminal approximation estimate. It did produce a concrete source-preserving route, an exact finite-dimensional formulation, an unconditional truncation counterexample, and a formalization specification.

All new results below are **DERIVED**: mathematical arguments supplied here, not new Lean-compiled declarations. Existing repository facts are identified by exact source and declaration. External classical results are identified separately. Numerical checks are consistency checks, not proof authority or interval certificates. No GitHub write was performed.

**Pinned repository:** `HMarcusWH/zeta-23-lean`  
**Commit:** `e6baabd98dc9d6c3228c168f786524604830e163`  
**Tree:** `09bb70b30fbfeac710cf7684f95e7d142f305fe2`

The live PR read at the start of this continuation agreed with that commit. The uploaded repository ZIP used for mathematical inspection is the previously authenticated snapshot of that tree. The continuation does not silently substitute a newer checkout.

The previous pass established an explicit imaginary-measure detector and generic causal-range countermodels. This pass follows the actual floor kernel rather than searching the same dependency contacts again. It does not repeat the full graph census.

### Main findings

1. A **different stable forcing built from the same original source and completion kernels** detects any off-line zero by a zeroth-order Laplace functional. No derivative of zeta and no simplicity assumption occur.
2. A finite dictionary of completed, shifted sources produces an exact positive-definite Gram problem. Its entire target column is explicit: apart from its first entry, it is a known constant times `1/n²`.
3. A logarithmic change of variables identifies the problem with a concrete compactly supported good kernel in the generalized strong Nyman–Beurling framework. Thus the global approximation target is an RH criterion, not an already-proved smallness estimate.
4. The locally finite integer expansion of the stable completed probe has ordinary partial sums whose `L²` norms diverge **unconditionally**. Computing the Gram matrix by that uncompleted expansion is invalid.
5. An explicit source-product lower bound turns any sufficiently small, rigorously enclosed finite residual into a **zero-exclusion certificate for a specified compact region**.
6. The proposed package has **23 core proof contracts**, **2 optional classical-transfer contracts**, and a separately labelled **OPEN terminal estimate**. Contract count is not a novelty count.

---

## 1. Frozen objects and conventions

Work in the complex Hilbert space `H = L²(0,∞)`, equivalently the repository's closed causal subspace of full-line `L²`. The inner product is conjugate-linear in its first slot and linear in its second:

\[
\langle f,g\rangle=\int_0^\infty\overline{f(t)}g(t)\,dt.
\]

The causal delay is `D_L f(t) = 1_{t≥L} f(t-L)` for `L≥0`. The Laplace transform is

\[
\mathcal L f(z)=\int_0^\infty e^{-zt}f(t)\,dt.
\]

Set \(\sigma=1/4096\). Preserve the literal original source

\[
j=P^2q,\qquad P=\partial_t^2-\tfrac14,
\]

where `q` is the original smooth, even probability density supported in `[-σ,σ]`. This is the source exposed by `OriginalSincNativeSource.lean`, not a replacement bump and not a detector autocorrelation.

Let

\[
J(z)=\int_\mathbb R e^{-zt}j(t)\,dt
=(\tfrac14-z^2)^2 Q(iz).
\]

The repository proves this exact one-copy-\(Q\) formula and its nonvanishing at an actual off-line zero. In particular,

\[
J(0)=\tfrac1{16},\qquad J(\tfrac12)=J(-\tfrac12)=0,
\]

and \(J\) is even and real on the real axis. The zeros at `±1/2` are at least double.

### A necessary causal adapter

The original \(j\) is supported on a symmetric interval. It is not itself a causal vector. Define the literal delay

\[
j_+(t)=j(t-\sigma),\qquad
\operatorname{supp}j_+\subset[0,2\sigma],\qquad
J_+(z)=e^{-\sigma z}J(z).
\]

This is a proved delay of the original source. It must not be implemented by silently redefining `nativeOriginalSource`. All identities below retain the delay factor until it legitimately cancels.

The signed rational kernel and positive floor kernel are

\[
c(t)=\mathbf1_{t\ge0}[-e^{-t/2}+2e^{-3t/2}],
\]

\[
a(t)=\mathbf1_{t\ge0}e^{-3t/2}
\lfloor e^t\rfloor\big(\lfloor e^t\rfloor+1-e^t\big).
\]

Their multipliers are

\[
R(z)=\frac{z-\frac12}{(z+\frac12)(z+\frac32)},\qquad
A(z)=R(z)\zeta(z+\tfrac12).
\]

The actual `a` satisfies `0≤a(t)≤e^{-t/2}` on the positive half-line. Its convolution operator is the existing
`nativeDampedCompletionCausalL2Operator 0 (le_rfl)`. The repository proves a strict norm bound below `605/621`.

The product identity for \(A\) is used away from \(z=1/2\). At that point the actual transform is \(A(1/2)=1/2\), not zero. A formalization must preserve this removable-pole distinction.

Finally, with the locally finite integer action

\[
(\mathcal N f)(t)=\sum_{n\ge1}\frac1{\sqrt n}f(t-\log n),
\]

the repository establishes \(a=\mathcal N c\). Local finiteness is not global `L²` convergence.

### Reused declarations

- `nativeOriginalSource_supported`, `nativeOriginalSource_contDiff`, `nativeOriginalSource_integral`.
- `nativeOriginalSourceLaplace_formula`, `nativeOriginalSourceLaplace_ne_zero_at_off_line_zero`.
- `nativeIntegerTranslateAction_rationalKernel_eq_positiveCompletion`.
- `nativeRationalCausalKernel_complexLaplace`.
- `nativePositiveCompletion_complexLaplace` and the separate `_half` theorem.
- `nativeDampedCompletionCausalL2Operator`.
- `native_coefficients_moebius_inverse`.
- The causal Laplace witnesses and the existing all-multiplicity Laguerre residual bounds.

Exact files, hashes and source line locators are in `SOURCE_INDEX.json`.

---

## 2. A simpler forcing with the same arithmetic completion

Define two real causal vectors

\[
v=c*j_+,\qquad w=a*j_+=Tj_+,
\]

where \(T\) is convolution by the actual \(a\).

Both are in `L¹∩L²`: use \(a,c\in L^1\), compact smooth \(j_+\in L^1\cap L^2\), and Young's inequality. No prime-field `L²` hypothesis is used.

Their transforms are

\[
V(z):=\mathcal L v(z)=R(z)J_+(z),
\qquad
W(z):=\mathcal L w(z)=A(z)J_+(z).
\]

Causal convolution and the locally finite integer identity give

\[
w=\mathcal N v.
\]

This identity is pointwise/local. Section 7 shows why it cannot be promoted to convergence of ordinary partial sums in `L²`.

### Zeroth-order off-line-zero obstruction

Fix an actual nontrivial right-half zero \(\rho\), and write

\[
\lambda=\rho-\tfrac12,\qquad\delta=\Re\lambda>0.
\]

The bounded functional

\[
\ell_\lambda(f)=\int_0^\infty e^{-\lambda t}f(t)\,dt
\]

has norm \((2\delta)^{-1/2}\). Since \(A(\lambda)=0\),

\[
\ell_\lambda(Tf)=A(\lambda)\ell_\lambda(f)=0
\quad(f\in H).
\]

But the source-visibility theorem gives

\[
\ell_\lambda(v)=R(\lambda)e^{-\sigma\lambda}J(\lambda)\ne0.
\]

The rational factor is nonzero at this parameter: the zero at `λ=1/2` would correspond to `ρ=1`, which is not a nontrivial zero.

Consequently,

\[
\boxed{\operatorname{dist}(v,\overline{\operatorname{Ran}T})
\ge \sqrt{2\delta}\,|V(\lambda)|>0.}
\tag{2.1}
\]

This uses only a zeroth-order witness even if \(\rho\) has high multiplicity. The original completed input has a leading jet involving a zeta derivative; the new target does not.

### A precise sufficient condition

\[
\boxed{v\in\overline{\operatorname{Ran}T}\Longrightarrow\mathrm{RH}.}
\tag{2.2}
\]

Reflect a hypothetical left-half zero to the right and apply (2.1).

This is a **conditional closing interface**, not a proof of the membership premise. It is also a different target from `nativeCompletedInput`: no theorem is allowed to identify the two without a separate proof.

### Dependency compression

The route requires the actual `j,c,a` construction, source visibility, causal Hilbert calculus and a prospective approximation estimate. It does not require every one of the 100 OPICA roots. The role of the wider inventory is to supply adapters, restrictions, countercontrols and alternative estimates, not to inflate the dependency chain.

---

## 3. Exact finite Gram formulation

For \(n\ge1\), define

\[
u_n=n^{-1/2}D_{\log n}j_+,\qquad
g_n=Tu_n=n^{-1/2}D_{\log n}w.
\]

For \(N\ge1\), let

\[
G_N=(\langle g_m,g_n\rangle)_{1\le m,n\le N},\quad
b_N=(\langle g_n,v\rangle)_{1\le n\le N},\quad
q_0=\|v\|^2.
\]

### Strict positive definiteness is provable

Suppose \(\sum_{n\le N}x_ng_n=0\). Taking Laplace transforms on the positive real axis gives

\[
W(z)\sum_{n\le N}x_n n^{-z-1/2}=0.
\]

For real \(z>1\), \(A(z)>0\) and \(J_+(z)>0\), so \(W(z)\ne0\). Divide by this nonzero quantity. If \(n_0\) is the least index with \(x_{n_0}\ne0\), multiply by \(n_0^{z+1/2}\) and let \(z\to\infty\). The remaining terms vanish and give \(x_{n_0}=0\), a contradiction.

Thus \(G_N\) is Hermitian positive definite. No generic invertibility assumption is smuggled in.

The best squared approximation error is exactly

\[
\boxed{d_N^2
=\inf_{x\in\mathbb C^N}\left\|v-\sum_{n\le N}x_ng_n\right\|^2
=q_0-b_N^*G_N^{-1}b_N.}
\tag{3.1}
\]

Equivalently, it is the bordered Gram determinant divided by \(\det G_N\). The sequence \(d_N\) is nonincreasing.

Every \(g_n\) is an actual causal output of \(T\), so

\[
d_N\ge \sqrt{2\delta}|V(\lambda)|
\tag{3.2}
\]

at any hypothetical right-half zero.

### The exact OPEN terminal estimate

\[
\boxed{\lim_{N\to\infty}d_N=0.}
\tag{C1}
\]

C1 would imply (2.2), hence close this route.

Generic Gram positivity only proves \(b_N^*G_N^{-1}b_N\le q_0\). C1 needs the opposite asymptotic information: that this quantity approaches \(q_0\) from below. Positive semidefiniteness is not the desired estimate.

### Incremental identity

Writing the enlarged Gram matrix as
\(\begin{pmatrix}G_N&h\\h^*&\gamma\end{pmatrix}\), its innovation denominator is

\[
s_N=\gamma-h^*G_N^{-1}h>0.
\]

Then

\[
d_N^2-d_{N+1}^2
=\frac{|b_{N+1}-h^*G_N^{-1}b_N|^2}{s_N}.
\tag{3.3}
\]

This supplies a useful monitored quantity. Small individual target coefficients do not imply small information gain when the innovation denominator is also small. Conversely, an ill-conditioned matrix is not by itself evidence of a useful gain.

---

## 4. The target column is explicit

The moment \(J_+(-1/2)=0\) removes the slow exponential from \(v\). For \(t\ge2\sigma\),

\[
v(t)=2J_+(-3/2)e^{-3t/2}.
\tag{4.1}
\]

Indeed, expand the convolution by the two exponentials and use that the whole source is included once \(t\ge2\sigma\).

Because \(2\sigma<\log2\), for every \(n\ge2\),

\[
\begin{aligned}
b_n
&=n^{-1/2}\int_0^\infty w(u)v(u+\log n)\,du\\
&=\frac{2J_+(-3/2)W(3/2)}{n^2}.
\end{aligned}
\]

Now \(R(3/2)=1/6\), \(A(3/2)=\zeta(2)/6\), and the delay factors cancel. Set

\[
C=\frac{J(-3/2)J(3/2)}3=\frac{J(3/2)^2}3>0.
\]

Then

\[
\boxed{b_n=C\frac{\zeta(2)}{n^2}\quad(n\ge2).}
\tag{4.2}
\]

For the first entry, use \(w=\mathcal N v\). Here the pairing interchange is justified: for \(n\ge2\) its absolute value integral is bounded by a constant times \(n^{-2}\). Therefore

\[
\boxed{b_1=q_0+C(\zeta(2)-1).}
\tag{4.3}
\]

Thus the unknown asymptotics sit in the actual arithmetic Gram matrix, not in an unspecified target column.

### The constant is itself tightly bounded from the actual source

Since \(q\) is an even probability density on `[-σ,σ]`,

\[
1\le Q(3i/2)=\int q(t)\cosh(3t/2)\,dt\le\cosh(3\sigma/2).
\]

As \(J(3/2)=4Q(3i/2)\),

\[
\frac{16}{3}\le C\le\frac{16}{3}\cosh^2(3\sigma/2)
\le\frac{16}{3}\left(\frac{134217728}{134217719}\right)^2.
\tag{4.4}
\]

The final bound uses \(\cosh x\le(1-x^2/2)^{-1}\) at \(x=3/8192\). These are source-derived bounds, not a numerical replacement of the infinite sinc density.

### A compact correlation core

Let \(K_v(L)=\int_0^\infty v(t)v(t+|L|)\,dt\). For \(|L|\ge2\sigma\),

\[
K_v(L)=C e^{-3|L|/2}.
\]

Consequently \(K_v(L)-C e^{-3|L|/2}\) is supported in `[-2σ,2σ]`. For
\(h_n=n^{-1/2}D_{\log n}v\), separated shifts satisfy

\[
\langle h_m,h_n\rangle=C\,\frac{\min(m,n)}{\max(m,n)^2}
\quad\text{when }|\log(m/n)|\ge2\sigma.
\tag{4.5}
\]

For \(m=n\), the value is \(q_0/n\).

All distinct shifts with indices at most 2048 satisfy the separation condition. Hence, for \(1\le K\le2048\),

\[
\left\|\sum_{n\le K}h_n\right\|^2
=CK+(q_0-C)H_K.
\tag{4.6}
\]

**This is the Gram matrix of shifts of \(v\), not the matrix \(G_N\) of shifts of \(w\).** Conflating them is a serious error. The full arithmetic completion cannot be inserted into (4.5) through an unjustified infinite double sum.

---

## 5. The phase-sensitive spectral formulation

Pass the actual transform identity to the imaginary axis using `a∈L¹` and continuity. This is an adapter to prove; it is not substitution into a half-plane theorem outside its domain.

For a Dirichlet polynomial

\[
P_N(s)=\sum_{n\le N}x_n n^{-s},
\]

Plancherel gives

\[
\left\|v-\sum_{n\le N}x_ng_n\right\|^2
=\frac1{2\pi}\int_{\mathbb R}
|R(i\xi)J(i\xi)|^2
|1-\zeta(\tfrac12+i\xi)P_N(\tfrac12+i\xi)|^2\,d\xi.
\tag{5.1}
\]

The source delay disappears only in this norm. Also,

\[
|R(i\xi)|^2=\frac1{\xi^2+9/4},
\]

so the exact weight is

\[
\Omega(\xi)=\frac{|J(i\xi)|^2}{2\pi(\xi^2+9/4)}
=\frac{(\xi^2+1/4)^4|Q(\xi)|^2}{2\pi(\xi^2+9/4)}.
\tag{5.2}
\]

The square of \(Q\)'s modulus occurs because this is an energy. It does **not** replace the original one-copy source transform.

This formulation keeps the cross term involving \(\zeta P_N\), not just the positive power spectrum \(|\zeta|^2\). The previous twin-kernel countermodel showed why `T*T` alone cannot determine causal range. Here the target column supplies additional, phase-sensitive information through the actual integer completion identity.

C1 is the statement that the infimum of (5.1) over finite Dirichlet polynomials tends to zero. It is not a consequence of the finiteness or positivity of the weight.

---

## 6. Exact connection to the generalized strong Nyman–Beurling framework

This is a literature connection with checked hypotheses, not a novelty claim.

Use the unitary change of variables

\[
(\mathcal U f)(t)=e^{-t/2}f(e^{-t}),
\qquad
f(x)=x^{-1/2}v(-\log x)\quad(x>0),\quad f(0)=0.
\]

Since \(v\) is causal, \(f(x)=0\) for \(x>1\). Formula (4.1) gives

\[
f(x)=2J_+(-3/2)x\quad(0<x\le e^{-2\sigma}).
\]

At \(x=1\), the delayed smooth source and its causal convolution have the needed flat matching to zero. Thus \(f\) is a continuously differentiable compactly supported good kernel. In particular,
\(\int x|f'(x)|dx<\infty\).

Moreover,

\[
\int_0^\infty f(x)\,dx=V(1/2)=0.
\]

For the classical Müntz operator

\[
(Pf)(x)=\sum_{n\ge1}f(nx)-\frac1x\int_0^\infty f(y)\,dy,
\]

the subtraction term is zero. Direct change of variables proves

\[
\mathcal U(Pf)=w,\qquad
\mathcal U[(Pf)(n\,\cdot)]=g_n.
\tag{6.1}
\]

The Mellin transform is

\[
\widehat f(s)=V(s-\tfrac12)
=e^{-\sigma(s-1/2)}
\frac{s(s-1)^3}{s+1}Q(i(s-\tfrac12)).
\tag{6.2}
\]

The generalized strong Nyman–Beurling theorem of Báez-Duarte gives
RH ⇒ \(f\in\overline{\operatorname{span}\{(Pf)(n\cdot):n\ge1\}}\)
for good kernels. Applying (6.1) yields RH ⇒ C1. The converse was proved directly in Section 2 from actual source visibility.

Therefore, **at the level of classical mathematics with that published theorem included**,

\[
\boxed{\mathrm{RH}\Longleftrightarrow d_N\to0.}
\tag{6.3}
\]

There is no need to claim the Mellin transform has no zeros throughout the entire strip: the native sinc transform may have zeros on the critical line. Our direct converse only needs nonvanishing at off-line zeros.

### Formalization boundary

The repository search did not locate a Lean formalization of the strong Nyman–Beurling theorem in its project source. Thus the reverse direction is an **optional classical-transfer work package**, not an available import and not a project axiom. The core sufficient criterion and finite regional certificates do not need it.

### What this connection changes

It proves that the chosen approximation problem is not an unnecessarily stronger arbitrary demand. It also identifies the analytic difficulty precisely. Classical work already studies these approximation mechanisms; optimal rates in related formulations can require RH and additional derivative hypotheses. Such conditional estimates cannot be used as independent closing inputs.

Primary sources:
- L. Báez-Duarte, *A general strong Nyman–Beurling criterion for the Riemann hypothesis*, arXiv:math/0505453, Theorem 1.2.
- L. Báez-Duarte, *A strengthening of the Nyman–Beurling criterion for the Riemann hypothesis*, arXiv:math/0202141.
- J.-F. Burnol, *A lower bound in an approximation problem involving the zeros of the Riemann zeta function*, arXiv:math/0103058.
- S. Bettin, J. B. Conrey and D. W. Farmer, *An optimal choice of Dirichlet polynomials for the Nyman–Beurling criterion*, arXiv:1211.5191: its stated optimal-rate result is conditional and is not an admissible closing premise.

---

## 7. Two different truncation failures

### 7.1 Unconditional failure of the ordinary integer partial sums

Let

\[
w_K(t)=\sum_{n\le K}n^{-1/2}v(t-\log n).
\]

For each fixed \(t\), this is eventually exactly \(w(t)\). Nevertheless, for
\(t\ge\log K+2\sigma\),

\[
w_K(t)=J_+(-3/2)K(K+1)e^{-3t/2}.
\]

Therefore its squared tail norm is exactly

\[
\boxed{
\int_{\log K+2\sigma}^\infty |w_K(t)|^2dt
=C e^{-3\sigma}\frac{(K+1)^2}{K}.
}
\tag{7.1}
\]

Hence \(\|w_K\|\to\infty\), whereas \(w\in L^2\). In particular,
\(\|w_K-w\|\to\infty\).

This does not assume an off-line zero. It is an unconditional boundary-layer effect of truncating the actual integer completion.

**Consequences:** do not compute \(G_N\) by assuming that
\(\mathcal N_Kv\to w\) in `L²`; do not exchange the full double integer sum with the Gram integral without a separate renormalized argument.

### 7.2 Conditional failure of raw Möbius truncation

Define the locally finite field

\[
M(t)=\sum_{n\ge1}\mu(n)n^{-1/2}j_+(t-\log n).
\]

The arithmetic convolution identity \(\mu*1=\delta_1\) gives
\(\mathcal NM=j_+\) locally, and causal convolution gives \(a*M=v\) locally. Neither identity proves \(M\in L^2\).

For the finite truncation \(M_N\), define \(e_N=v-TM_N\). It is zero for \(t<\log(N+1)\). At a hypothetical zero \(\lambda\),

\[
\ell_\lambda(e_N)=V(\lambda).
\]

Cauchy–Schwarz restricted to the tail yields

\[
\boxed{\|e_N\|\ge
\sqrt{2\delta}|V(\lambda)|(N+1)^\delta.}
\tag{7.2}
\]

Thus the raw Möbius approximants would have exponentially growing error in logarithmic time under that obstruction. This does not disprove C1: C1 minimizes over all coefficient vectors, not only the raw Möbius choice.

The repository's `MultiplicityTail.lean` already proves a stronger general all-multiplicity Laguerre barrier for its original residual family. That existing theorem is reused. Equation (7.2) is its simple zeroth-order analogue for the new forcing, not a claimed new general tail principle.

### A safe alternative for finite computation

Truncate the actual floor kernel in physical time:

\[
a^{[T]}=a\,\mathbf1_{[0,T]},\qquad
w^{[T]}=a^{[T]}*j_+.
\]

Then

\[
\|w-w^{[T]}\|_2
\le\|a-a^{[T]}\|_1\|j_+\|_2
\le2e^{-T/2}\|j\|_2.
\tag{7.3}
\]

This is a genuine convergent approximation. It is not the same operation as truncating the integer sum.

If \(\Delta_T=2e^{-T/2}\|j\|_2\), a finite Gram entry satisfies

\[
|G_{mn}-G^{[T]}_{mn}|
\le\frac{2\|w\|_2\Delta_T+\Delta_T^2}{\sqrt{mn}}.
\tag{7.4}
\]

These bounds can be pessimistic at the very small fixed source scale. They are nevertheless legitimate error budgets, unlike the divergent integer cutoff.

---

## 8. A quantitative causal-leakage barrier

Keep the undamped actual operator \(T\), now acting on full-line `L²`, and the hypothetical zero parameter \(\lambda\) above. The causal witness is

\[
\psi_\lambda(t)=\mathbf1_{t\ge0}e^{-\overline\lambda t}.
\]

Its adjoint image vanishes for \(t\ge0\). For \(u>0\),

\[
(T^*\psi_\lambda)(-u)
=e^{\overline\lambda u}
\int_u^\infty a(s)e^{-\overline\lambda s}\,ds.
\]

Using \(a(s)\le e^{-s/2}\),

\[
|(T^*\psi_\lambda)(-u)|
\le\frac{e^{-u/2}}{\delta+1/2},\qquad
\|T^*\psi_\lambda\|\le\frac1{\delta+1/2}.
\]

For an arbitrary full-line approximant \(f\), write \(f_-=f\,\mathbf1_{(-\infty,0)}\) and \(r=v-Tf\). Then

\[
|V(\lambda)|
\le\frac{\|r\|}{\sqrt{2\delta}}
+\frac{\|f_-\|}{\delta+1/2}.
\]

Thus

\[
\boxed{
\|f_-\|\ge
(\delta+\tfrac12)
\left(|V(\lambda)|-\frac{\|v-Tf\|}{\sqrt{2\delta}}\right)_+.
}
\tag{8.1}
\]

A successful full-line inverse cannot silently count as a causal inverse. If it drives the output error below the witness margin, it must carry a definite negative-time input under the hypothetical obstruction.

No existence of a full-line inverse for the actual multiplier is asserted. Equation (8.1) applies to any approximant that exists. The previous positive twin-kernel example supplies a falsification control where such noncausal inversion does exist.

---

## 9. Multi-zero and multiplicity-aware dual certificates

For distinct \(\lambda_i\) with positive real parts and positive integers \(m_i\), use

\[
\psi_{i,k}(t)=t^k e^{-\overline{\lambda_i}t}\mathbf1_{t\ge0},
\quad 0\le k<m_i.
\]

Their exact Gram matrix is

\[
\mathsf G_{(i,k),(j,l)}
=\frac{(k+l)!}{(\lambda_i+\overline{\lambda_j})^{k+l+1}}.
\tag{9.1}
\]

It is positive definite. Its confluent Cauchy determinant is

\[
\det\mathsf G=
\frac{
 \displaystyle\prod_i\prod_{k=0}^{m_i-1}(k!)^2
 \prod_{i<j}|\lambda_i-\lambda_j|^{2m_im_j}
}{
 \displaystyle\prod_i(2\Re\lambda_i)^{m_i^2}
 \prod_{i<j}|\lambda_i+\overline{\lambda_j}|^{2m_im_j}
}.
\tag{9.2}
\]

One proof starts from the ordinary Cauchy determinant and takes divided-difference confluent limits, retaining the factorial normalization. This matches the exact symbolic tests in the package.

If all witnesses annihilate `Ran T` and \(b_{i,k}=\langle\psi_{i,k},v\rangle=(-1)^kV^{(k)}(\lambda_i)\), then

\[
\boxed{\operatorname{dist}(v,\overline{\operatorname{Ran}T})^2
\ge b^*\mathsf G^{-1}b.}
\tag{9.3}
\]

Adding witnesses cannot decrease this lower bound. The new target's derivatives involve its explicit source/rational transform, not derivatives of zeta.

For the old completed input, where only the leading jet is nonzero, the single-node inverse entry reproduces the existing Laguerre constant
\((2\Re\lambda)^{2m-1}/((m-1)!)^2\). That is a normalization/reuse check, not a rediscovery claim.

The finite witnesses need not be complete in the entire adjoint kernel. No completeness assertion, missing singular-inner-factor argument, or infinite inverse is used.

---

## 10. From finite residuals to genuine zero-exclusion certificates

Let

\[
K=\{\lambda:\delta_0\le\Re\lambda\le\delta_1,\ |\lambda|\le L\},
\quad 0<\delta_0\le\delta_1<1/2,\quad L\ge\delta_1.
\]

An explicit positive lower bound for \(\sqrt{2\Re\lambda}|V(\lambda)|\) on \(K\) can be computed from the fixed source product.

The product widths are \(a_n=\sigma/[n(n+1)]\), \(n\ge1\), and

\[
Q(i\lambda)=\prod_{n\ge1}\frac{\sinh(a_n\lambda)}{a_n\lambda}.
\]

### Small-factor estimate

For \(|z|\le1/2\),

\[
\left|\frac{\sinh z}{z}-1\right|\le |z|^2/3,
\qquad
\log\left|\frac{\sinh z}{z}\right|\ge-2|z|^2/3.
\]

The first bound follows directly from the power series; the second uses
\(\log(1-u)\ge-2u\) for \(0\le u\le1/2\).

If \(\sigma L\le1\), all factors are small, and
\(\sum a_n^2\le\sigma^2/2\) gives

\[
B_Q=\exp(-\sigma^2L^2/3)\le |Q(i\lambda)|.
\tag{10.1}
\]

Otherwise choose \(M\ge1\) with
\(\sigma L/[(M+1)(M+2)]\le1/2\).
For the first \(M\) factors use

\[
|\sinh(a_n\lambda)|\ge\sinh(a_n\delta_0)\ge a_n\delta_0.
\]

For the tail use
\(\sum_{n>M}a_n^2\le\sigma^2/(3M^3)\).
This yields the explicit, potentially weak but positive bound

\[
B_Q=
(\delta_0/L)^M
\exp[-2\sigma^2L^2/(9M^3)]
\le |Q(i\lambda)|.
\tag{10.2}
\]

Since

\[
V(\lambda)
=e^{-\sigma\lambda}
\frac{(\lambda-1/2)^3(\lambda+1/2)}{\lambda+3/2}Q(i\lambda),
\]

we obtain

\[
\boxed{
\Gamma_K=
\sqrt{2\delta_0}\,e^{-\sigma\delta_1}
\frac{(1/2-\delta_1)^3(1/2+\delta_0)}{L+3/2}B_Q
\le\sqrt{2\Re\lambda}|V(\lambda)|.
}
\tag{10.3}
\]

No numerical zero or RH premise enters this product bound.

### Finite certificate theorem

If a finite coefficient vector satisfies

\[
\left\|v-\sum_{n\le N}x_ng_n\right\|<\Gamma_K,
\tag{10.4}
\]

then \(\zeta(1/2+\lambda)\ne0\) for every \(\lambda\in K\).

This follows immediately from (3.2). Thus Round 2 has a finite, independently checkable output even before an all-\(N\) theorem is found.

No such region certificate was produced in this pass. The current computation tested algebraic and analytic bounds; it did not evaluate a certified canonical Gram matrix.

### Sound numerical contract

For any rational-complex trial vector \(x\),

\[
E_x^2=q_0-2\Re(x^*b)+x^*Gx
\]

is an upper bound for \(d_N^2\). One does not need to invert an interval matrix.

Suppose
\(q_0\le q^+\),
\(\|b-\tilde b\|\le\epsilon_b\),
\(\|G-\tilde G\|\le\epsilon_G\).
Then

\[
E_x^2\le
q^+-2\Re(x^*\tilde b)+x^*\tilde Gx
+2\|x\|\epsilon_b+\|x\|^2\epsilon_G.
\tag{10.5}
\]

A certified upper value below \(\Gamma_K^2\) proves (10.4). A failed enclosure returns `NO_CERTIFICATE`; it is not a falsification of the underlying criterion.

For a two-sided finite residual enclosure, use
\(r=b-Gx\) and a certified \(G\succeq\ell I\), \(\ell>0\):

\[
E_x^2-\|r\|^2/\ell\le d_N^2\le E_x^2.
\tag{10.6}
\]

Conditioning and cancellation must be included. In particular, at scale \(1/4096\), a small relative error in a large energy may be useless for the very small absolute threshold.

---


### Certified approximation of the original source, not a substitute source

There is also a source-correct route to finite computation. Let \(q_M\) be the convolution of the first \(M\) specified uniform boxes and let \(\mu_{>M}\) be the actual tail probability law. The repository already supplies the prefix/tail convolution identity and tail support. Thus

\[
q=q_M*\mu_{>M},\qquad
\operatorname{supp}\mu_{>M}\subset[-\sigma/(M+1),\sigma/(M+1)].
\]

Set \(j_M=P^2q_M\). For a sufficiently smooth fixed prefix (for example \(M\ge12\)), derivative transport gives
\(j=j_M*\mu_{>M}\).

Translation estimates yield

\[
\|j-j_M\|_2\le\frac{\sigma}{M+1}\|j_M'\|_2.
\tag{10.7}
\]

More usefully, the tail is centered and its variance is

\[
v_M=\frac{\sigma^2}{3}\sum_{n>M}\frac1{n^2(n+1)^2}
\le\frac{\sigma^2}{9M^3}.
\]

The linear Taylor term cancels, giving

\[
\|j-j_M\|_2\le\frac{v_M}{2}\|j_M''\|_2.
\tag{10.8}
\]

For the variance-corrected approximation
\(\tilde j_M=j_M+\frac{v_M}{2}j_M''\), symmetry removes odd terms and
\(\mathbb E[Y^4]\le3v_M^2\) gives

\[
\boxed{\|j-\tilde j_M\|_2
\le\frac{v_M^2}{8}\|j_M^{(4)}\|_2.}
\tag{10.9}
\]

These follow from integral Taylor remainder bounds in `L²`, not pointwise Taylor convergence. Uniform derivative bounds can be taken from a fixed smooth prefix because convolution by later probability laws is an `L²` contraction.

The finite-prefix source and its variance correction retain the two killed exponential moments, evenness and mass normalization. They nevertheless remain **approximations**, accompanied by (10.7)–(10.9), not replacements for the canonical source.

If the source error is \(\eta\), the probe error is at most \(\|c\|_1\eta\), and the completed-probe error is at most \(\|a\|_1\eta<\eta\). Combine these with the physical-time cutoff and quadrature errors before issuing a certificate. The bounds can still be numerically expensive at the prescribed small scale; no practical precision or complexity claim is made here.


## 11. OPICA Round 2 specification

The proposed namespace is `Zeta23.OPICARound2`, not the existing paper's `R2-*` namespace. Existing 100-root contracts, original sources and accepted evidence stay frozen.

### Work packages and exact output

| Package | Core contracts | Deliverable |
|---|---|---|
| A. Causal source and probe | P01–P05 | Literal delay, stable vectors, actual transform identities, multiplicity-free separation and conditional sufficiency |
| B. Exact Gram reduction | P06–P12 | Tail/correlation formulas, explicit target column, positive-definite finite matrix, Schur error, innovation identity, spectral norm and sufficient limit criterion |
| C. Truncation and causality controls | P13–P16 | Local Möbius inverse, unconditional integer-truncation failure, conditional Möbius barrier, safe physical cutoff, noncausal leakage budget |
| D. Dual and certified finite computation | P17–P19 | Confluent witness Gram, simultaneous separation and sound residual enclosures |
| E. Classical adapter and regional output | P20–P22 | Compact Müntz kernel, explicit native product lower bound, finite region-exclusion theorem |
| F. Certified original-source approximation | P23 | Prefix/tail source error, centered-variance improvement and variance-corrected remainder |
| G. Optional classical equivalence | P24–P25 | A genuine formal proof/import of the strong Nyman–Beurling necessity direction and resulting iff; no axiom placeholder |

`ROUND2_CONTRACTS.json` gives exact statements, inputs, forbidden substitutions, proof sketches and acceptance requirements for every contract. The two classical-transfer contracts are optional because the core forward criterion and regional certifier do not need them.

### The critical separation

The following is **not** a completed theorem in the package:

> C1: the actual finite Gram residual \(d_N\) tends to zero.

It remains the terminal research target. No acceptance requirement may silently replace proving C1 by proving `C1 → RH`.

### Minimal implementation sequence

1. P01–P07 and P23: construct and audit the actual probe and its target column.
2. P08–P12 plus P19: obtain the finite exact problem and a sound evaluation interface.
3. P14 and P21–P22: make computation tail-controlled and able to issue regional certificates.
4. P13, P15–P18: strengthen countercontrols and simultaneous witnesses.
5. P20: identify the classical framework exactly.
6. P24–P25 only if the classical formalization cost is justified; never block the core investigation on an unavailable import.

At each stage require actual Lean compilation, standard-axiom audits, independently written expected types, tests that deliberately violate the source/domain conditions, and a source-pinned receipt. No new project axiom, no `sorry`, no copied-signature-only review.

### Required falsification controls

The full machine-readable list is in `ROUND2_CONTRACTS.json`; the critical ones are:

- Using symmetric \(j\) as an already causal vector.
- Replacing one-copy \(Q\) source visibility by the detector autocorrelation.
- Treating `A(1/2)` as zero.
- Calling the new probe the old completed input.
- Inferring global `L²` membership from a locally finite Möbius identity.
- Using ordinary integer partial sums as an `L²` approximation.
- Interchanging the nonconvergent double integer Gram sum.
- Dropping the conjugation/factorials in the witness Gram matrix.
- Dropping the negative-time input cost in a full-line inverse.
- Replacing the Gram matrix of \(w\)-shifts by the simpler Gram of \(v\)-shifts.
- Treating Gram positivity as an upper error bound approaching zero.
- Treating a floating-point inverse or an uncertified native-source approximation as a zero-exclusion certificate.

---

## 12. Reclassified routes and post-green implications

### What the existing verified mathematics contributes

The exact source visibility and floor-kernel transform allow a new stable probe. The Möbius coefficient identity supplies a literal local inverse. The already-proved Laguerre residual mechanism supplies the correct interpretation of truncation. The causal Hilbert interface keeps noncausal inverses from leaking into the argument.

### What changed in this pass

- The required obstruction pairing is zeroth order, even at multiple zeros.
- The arithmetic approximation target is a single fixed vector, not all inputs.
- The target column is explicit.
- There is a rigorous finite-output mode: exclude a compact zero region after a certified residual crosses its explicit threshold.
- A seemingly natural finite approximation was disproved without assuming any hypothetical zero.

### Upstream implications

The common abstraction is a source \(j\) with two specified moments, an actual rational kernel \(c\), and its integer completion \(a\). Keep this abstraction separate from the particular conjectural range-membership claim. The literal native specialization is mandatory.

### Downstream implications

The exact scalar column can support interval-certified Gram computations. The same probe can be used with multiple adjoint zero jets and with full-line inverse algorithms, provided their causal leakage is accounted for. Existing fixed-zero signed-measure tests remain useful, but need not be the only detector.

### Resurrected or narrowed routes

- A source-preserving Nyman–Beurling-type route is now explicitly connected to the project, rather than only suggested by analogy.
- Arbitrary fixed-basis uniformity is unnecessary for the single-witness contradiction.
- Naive integer or Möbius truncation is not resurrected; its missing global control is now quantified.
- Generic spectral positivity is still insufficient. The useful object is the joint source/target approximation data, not power data alone.

### Highest-leverage next move

Build the actual finite residual certifier and study the normalized innovations (3.3) on the exact native source. A substantive next theorem would control the sum of these gains, or construct a coefficient family with an independent upper bound in (5.1).

A purely finite decreasing sequence is not enough. Any numerical signal must be accompanied by tail, source, conditioning and quantifier controls before it can motivate a proposed all-\(N\) estimate.

---

## 13. Verification performed and limits

`research_checks.py` passes **1,083 checks** at 65 decimal digits where numerical arithmetic is used. These include:
- 1,000 exact Möbius divisor identities;
- exact rational-complex confluent determinant tests;
- exact single-jet/Laguerre and shifted-tail inverse entries;
- Schur residual and innovation identities;
- a direct floor-kernel moment calculation with an analytic tail bound;
- polynomial compact-source controls for the tail and target-column formulas;
- finite-product consistency tests for the actual sinc-product lower bounds at generic parameters;
- positive twin-kernel and noncausal-leakage countercontrols;
- integer-partial-sum tail growth and separated-shift Gram identities;
- centered tail-variance and variance-corrected source-approximation constants.

The polynomial test source is explicitly **not** the canonical infinite-sinc source. The native product tests do not assert that their parameters are zeta zeros. No actual canonical \(G_N\) was evaluated or certified in this pass. The numerical tests are not interval certificates.

No Lean compiler is available in this execution environment. Therefore none of these new paper-level deductions has been promoted to a formal declaration. The first implementation milestone is to compile the native probe and independently check its exact types.

## Conclusion

The continuation has not supplied the missing independent approximation estimate. It has supplied a detailed, falsifiable specification for the next round: a multiplicity-free actual-source probe, exact finite Gram residual, explicit mixed coefficients, compulsory truncation/causality controls, and a finite regional-exclusion interface.

The decisive open question is now concrete:

\[
\inf_{P_N}
\int_{\mathbb R}\Omega(\xi)
|1-\zeta(\tfrac12+i\xi)P_N(\tfrac12+i\xi)|^2d\xi
\longrightarrow0
\]

for the **exact native weight**, by an argument that does not assume the desired conclusion.

Everything claimed before that last step is kept distinct from the last step itself.


---

## Source: DEEP_SEARCH.md

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


---

## Source: ROUND2_POSTGREEN_V2_1.md

# OPICA Round 2 — post-green research and revised specification, v2.1

**Marcus Hermansson · Riemann Hypothesis research · 25 October 2026**  
**Disposition: Step 4 OPEN; RH OPEN.**  
**New Lean declarations compiled in this investigation: 0.**

## 1. Outcome


**Completeness revision 2.1.** A second pass found substantive omissions in v2.
Sections 2 and 10 now reflect the new source pin and expanded specification;
Section 15 contains the full omission audit, precise restored statements,
deferred-lane register and carry-forward decisions. The original v2 remains
in the package for comparison. The four additions are **S14 CT1 scalar limits,
S15 finite neutral approximation, S16 fixed-filter global sufficiency, and
S17 phase-complete positive observations**. None supplies the missing terminal
estimate. [C1–C8]

The investigation did not establish a global Step 4 closure. The completed
OPICA mathematics makes the remaining obligations much more precise, but none
of the independently checked workflow outputs supplies the required opposing
arithmetic estimate, causal approximation theorem, or outgoing-contact sign.

This document is the requested fallback: **a revised, source-pinned OPICA Round
2 handoff**, incorporating the three attached October 25 documents, the earlier
October 25 harvest and closure investigation, the current PR, and the current
Drive route dossiers. It preserves the original 25 proposed contracts and adds
17 explicitly proposed supporting amendments, including four restored by the completeness audit. The optional C2/C3/C4 programme, historical control registry, 49-requirement/WP carry-forward and complete module map are now explicit. Those numbers describe work
records, not new theorems or mathematical novelty. The four terminal research
targets remain separately OPEN.

The most useful changes to the preliminary Round 2 plan are concrete:

1. Retain the fixed-source causal probe, but do not begin with a small raw Gram
   optimization: the actual source gives a rigorous finite-size obstruction.
2. Make the **fixed, source-preserving filtered primal certificate** the first
   executable/formalization milestone. Its rational four-column baseline has
   been independently reconstructed here with exact arithmetic.
3. Carry the original source and transported dual witness through every filter.
   A small filtered norm without its corresponding witness margin proves nothing.
4. Add quantitative prefix constraints and adaptive error budgets. Successful
   coefficients must approach the actual Möbius coefficients at every fixed
   index, and input norms cannot remain bounded for the new undamped target.
5. Keep A, C, and D as genuine alternative analytic research routes. They are
   not discharged by formalizing the causal certificate infrastructure.
6. Preserve and strengthen the adversarial controls. A fresh paper deduction
   in this pass gives an ordered negative minor in the **literal native
   prime-plus-Archimedean jump gain**, excluding one tempting total-positivity
   shortcut without modifying the prime coefficients.

No repository source was edited, no PR was merged or posted to, and no existing
research contract was silently rewritten. The originals are included unchanged
in the companion package.

## 2. Exact evidence and coverage

### 2.1 Repository pin and authority

| Object | Verified identity or scope |
|---|---|
| PR | [HMarcusWH/zeta-23-lean #294](https://github.com/HMarcusWH/zeta-23-lean/pull/294), open draft at the inspected snapshot |
| Current inspected head | `416aec21d4d6634675639b5397cc300d1f826e34` |
| Current tree | `0506bca8ffe613e9cd9ab844650a1141d4494f66` |
| Accepted parent/base | `d53dd70d38b0762af130b1d19b795af259f505f5` |
| Delivered-v2 source | `f5bafbc575c5663cdfaa4ce9e1de69d9fb9f9486`, tree `fe6dd1dc24b590209bab629d9424348722aadd56` |
| Change from delivered v2 | Two workflow setup lines and eight generated metadata files; **no Lean or dependency-pin changes** |
| Native compiler/dependencies | Lean `4.33.0-rc2`; Mathlib `51e6992efd06126df61a496bebf8f49482a4e129` |
| Current workflow snapshot | **25 October 2026, 17:07:17 UTC / 18:07:17 Europe/Stockholm (CET)** |

At that dated snapshot, 22 current-head runs had 76 declared jobs: 51 successful,
12 in progress, one skipped and 12 not yet instantiated. No current failure was
observed. The complete ledger retains current status separately from historical
scientific dispositions; it does not represent the new head as fully green. [R1, C1]

The predecessor f5 full100 aggregate and dependency delta have now completed
and were independently downloaded and checked. The full receipt records
`COMPILER_VERIFIED_FULL_100`: 100 original roots, 28 units, 203 consumer queries,
83 definitions and 18 constructors. All 4,780 source-manifest hashes match the
predecessor checkout, including 1,353 Lean files. The three successful command
logs, compiled exporter hash and all 386 historical reviewed declaration-type
hashes match. The recorded 3,793 declarations use only the standard axiom set.
All 42 exported historical-review source hashes still match unchanged sources.
These are receipt/source checks; this investigation did not rerun Lean. [C1]

The same receipt explicitly has `release_ready=false`, `full_release_accepted=false`
and independent human review `NOT_ESTABLISHED`; RH, Step 4 and the closing
inequalities remain OPEN. The old generated-state gate failed because
`cryptography` was absent, and its summary failed the dependent gate. The new
head installs the already declared requirements. Old aggregate success is not
fresh current-head acceptance. [C1]

Exact root types still govern authority. A theorem `quiet complete observation
-> RH` does not establish quietness. A green wrapper does not turn a saved
`FALSIFIED`, `UNRESOLVED` or `NO_ELIGIBLE_INHERITED_CONTACT` result into a
positive theorem. The original-100 reuse crosswalk records each exact contract,
source, expected-type consumer and physical/domain consumer. [C1]

### 2.2 Drive and attachment coverage

The linked Drive folder was recursively enumerated live: **1,206 unique files
in 152 folders**, with no listing errors and no truncated folder page. The
expanded recensus at 16:57:17 UTC also compared IDs, title, size, modified time, MIME and file/folder kind: no additions, removals or selected metadata changes. This still does not certify unchanged bytes throughout the archive. Current
route dossiers, their original proofs, the latest OPICA papers and amendments,
and the current CI-triage note were reread selectively against the new live
repository pin. A dated Drive note pinned to an older commit does not override
current GitHub evidence. [R2]

The first pass fetched 21 targeted Drive texts. The reading ledger distinguishes
full reading, substantive section review and heading/keyword crosschecks;
the remaining live files have inventory-level coverage in this pass.

The expanded completeness pass fetched 16 more source records, with 13 full readings and three exact-section/schema reviews, and reread the named amendment and route papers. Its 22-record reading ledger preserves these scopes. All 40 direct project attachments now have an explicit disposition, and all 49 original requirements plus WP0–WP7 have a carry-forward map. Neither ledger claims every embedded proof page was reread. [C2, C3]

All 40 named project-source attachments were inventoried and extracted,
including nested archives. The extraction also recovered the October 20
handover's embedded source capsule: 1,466 documentary records, comprising 98
PDFs, 31 Word documents and 1,337 Markdown records. The combined origin ledger
contains 5,792 records and 3,790 unique content hashes, with no extraction
errors. Those are inventory/extraction counts, **not claims to have manually
read every page or proved every archived argument**. The reading ledger
separates substantive review from extraction, indexing, duplicates and inherited
review. The three attached OPICA files and both prior October 25 reports were
read in full. [R2, R3]

The recent state was reconstructed from the v2.9 master, PR292 handover,
Step 4 handovers, A/B/C rounds, the Path D first-contact and ESET-transfer notes,
OPICA's original/followup contracts, and current source declarations. Older
deconvolution, first-contact, canonical-ratio, toolkit and historical-route
documents were used to identify which failed routes had actually acquired a
missing prerequisite. Cross-project material supplies possible methods; it
does not supply a native zeta hypothesis or theorem by analogy.

### 2.3 A naming trap to avoid

The modern **Paths A–D** in this report are the four Step 4 research routes below.
The older CI workflow's **Tracks A–D** use different labels for source/ground
transfer, canonical Schur domination, spectral identification and visibility.
In particular, a green legacy “Track D” job is not a proof of the modern
pole-neutral Path D exit theorem. The workflow appendix preserves its original
names and scopes. A third naming convention occurs in the October 12 requirements: its Track B concerns first-negative propagation and maps mainly to current C/D, not causal B. The 49-ID crosswalk records that distinction. [R1, R2, C2]

## 3. What steps 1–3 now contribute

| Step | Mathematical content now usable | What it does not establish |
|---|---|---|
| 1: fingerprint | An actual off-line zero gives a source-visible, sign-sensitive obstruction with its correct multiplicity and original source | An independent upper bound excluding that obstruction |
| 2: no-hide | Canonical scales and witness-generation results prevent a hypothetical off-line zero from evading every detector | Positivity of every detector or nonexistence of the zero |
| 3: synchronized tracking | The checked consumers keep the same generated state, source, zero, phase/history, multiplicity, transformations and quantitative obstruction; native fixed/slow-source rate theorems identify the retained exponential rate | A change of witness that discards the hard term, or a terminal sign/energy estimate |
| 4: contradiction | Exact conditional interfaces exist for the relevant closing estimates | None of their independent closing premises is proved by the present harvest |

The important new usable information relative to older handovers is the native
rate law. For the literal fixed source family and each fixed `C>1`,

$$
E_d(T;C)=\int_{T-C\log T}^{T}|F_d(t)|^2\,dt,
\qquad
\lim_{T\to\infty}\frac{\log(1+E_d(T;C))}{2T}=\Theta.
$$

Here `Theta` is the actual supremum of nontrivial-zero displacement from the
critical line, with the repository's precise definition. The slow-source
extension prices the schedule `d(T) log(d(T)+2)=o(T)`; it is not an unrestricted
license to send the source order to infinity. The complete fixed two-factor
raw and absorbed high-mask observations retain the same `Theta` rate. No
rightmost-zero or simple-zero hypothesis is required for these conclusions.
[R4]

In particular, the compiled `exists_generatedStep123CompleteOutput` and
`exists_eachPhase_cofinal_generatedStep123CompleteOutput` establish complete
same-packet existence and assembly from an actual off-line zero, any
`0<beta<|Re(rho)-1/2|`, a chosen parity and an arbitrary lateness bound. Cofinality
is available separately for each parity; this does not assert both phases at
one aperture or a witness at every sufficiently large aperture. The construction
is noncomputable and may use `Classical.choice`; it is not an executable search
algorithm. [R1]

Consequently, many earlier “maybe the transformation has made the signal
small” proposals can now be checked decisively. Preservation of the actual
positive rate and an independent strictly smaller upper would contradict each
other. Preservation alone is not the upper.

There is a separate evidence boundary in the large Step123 artifact: its
compiler export is valid for the statements it checks, while its universal
producer/independent-review flags must be reported literally. Do not confuse
those artifact completeness flags with either a failure of a compiled
same-state theorem or a completed universal 44-field release. [R1]

## 4. The four live closing obligations

### Path A — complete signed arithmetic

The target is an independently proved upper on the **complete, correctly
signed arithmetic observation**, including repeated-prime products, finite
palette corrections, collisions, lower masks and all cross terms. The current
rate theorem says its normalized logarithmic rate is `Theta`. A quiet upper
along one cofinal sequence would force `Theta=0`; proving the conditional
consumer again would not.

The earlier October 25 investigation obtains a strict upper on the three unit
axes of one arithmetic trace, with exponent `57/25+o(1)` below `5/2`. That result
has a paper proof and depends on the separately recovered external
seven-eighths theorem. It does **not** bound the whole Eisenstein annulus or
the full signed high-mask observation. The complementary sector and its mixed
terms remain the obstacle. [R5]

The exact balanced continuation is especially instructive. With the actual
finite mollifier `M_{Y,Q}`, corrected zeta factor `Z_Q`, and source transform,

$$\widehat{\mathsf B_Y^\infty}(z)
=\widehat F_m(z)\bigl(1-Z_Q(z)M_{Y,Q}(z)\bigr)^r.$$

At a hypothetical visible zero the factor in parentheses equals one. Increasing
`r`, differentiating the source with a nonzero return factor, or changing a
finite Euler palette does not attenuate the pole. A finite upper cutoff can
remove it from a finite transform, but the omitted continuation retains the
residue. Moving the cutoff past the observation window transfers the problem
to the annular handoff term; it does not estimate that term. [R6]

**Open research target A:** prove a genuinely smaller upper for the literal
complete observation, or a new estimate on its precisely defined complement
that composes with the established axis estimate. An absolute-value estimate
would suffice if it met the required exponent for the complete native object.
A weaker unsigned replacement or toy finite-mask computation does not.

A separate arithmetic-observation branch is now explicit: S10/S17 supply
fixed-direction or phase-complete negative-test margins. A source-matched
nonnegative physical observation with independently smaller total error would
also contradict the hypothetical zero. These linear measure observations have
their own source/recovery scope; they are not the registered high-energy object,
and neither their positivity nor their cheap recovery has been established. [C1, C6, C7]

### Path B — source-specific causal approximation

The old B–Y statement concerns the original completed input at every positive
damping. The proposed October 25 probe is a **different undamped target**.
Keep these two interfaces distinct.

Set `sigma=1/4096`, retain the original probability density `q`, and define

$$j=(D^2-\tfrac14)^2q,\qquad j_+(t)=j(t-\sigma).$$

Use the literal kernels

$$c(t)=\mathbf1_{t\ge0}(-e^{-t/2}+2e^{-3t/2}),$$

$$a(t)=\mathbf1_{t\ge0}e^{-3t/2}
\lfloor e^t\rfloor\bigl(\lfloor e^t\rfloor+1-e^t\bigr),\qquad Tf=a*f.$$

Then `v=c*jPlus`, `w=a*jPlus`, and

$$V(z)=R(z)e^{-\sigma z}J(z),\quad W(z)=A(z)e^{-\sigma z}J(z),$$

$$R(z)=\frac{z-1/2}{(z+1/2)(z+3/2)},\qquad
A(z)=R(z)\zeta(z+1/2),$$

with the removable-pole point treated separately: `A(1/2)=1/2`. An off-line
zero `rho=1/2+lambda`, `delta=Re(lambda)>0`, gives the actual-source separation

$$\|v-Tf\|_2\ge\sqrt{2\delta}\,|V(\lambda)|>0
\quad\text{for every causal }f\in L^2(0,\infty).$$

This zeroth-order witness handles multiple zeros without a derivative lower
bound. Its existence is a useful simplification of the obstruction. The
opposing estimate remains open. [R7]

For `g_n=n^{-1/2}D_{log n}w`, the finite least-squares data are

$$G_N=(\langle g_m,g_n\rangle),\quad b_N=(\langle g_n,v\rangle),\quad q_0=\|v\|_2^2,$$

$$d_N^2=q_0-b_N^*G_N^{-1}b_N.$$

The target column is explicit, with `C=J(3/2)^2/3`:

$$b_1=q_0+C(\zeta(2)-1),\qquad b_n=C\zeta(2)/n^2\quad(n\ge2).$$

**Open research target B:** exhibit actual finite coefficients with residual
tending to zero, or prove the actual `d_N -> 0` by an independent arithmetic
argument. At the classical paper level the generalized strong Nyman–Beurling
theorem identifies the original compact good-kernel version as an RH criterion.
The known optimal-rate theorem of Bettin–Conrey–Farmer assumes RH and an
additional inverse-derivative bound; it cannot close this implication without
circularity. [P1, P2]

The fixed-filter route now has its own conditional global consumer S16:
for the one fixed B of Section 7, finite trials with full filtered residual
norm tending to zero imply RH. Its proof keeps the positive Laplace witness
and does not invert B. This is an alternative sufficient premise to the raw
limit, and the existence of such a sequence remains OPEN. [C2]

### Path C — full continuous contact and original-detector energy

For the **original-detector Schur subroute**, retain the full original detector
and its complete complement. On the same cofinal family produced after fixing
a hypothetical zero and a smaller positive exponent `beta`, the existing lower
obstruction has the form

$$S_n>\tfrac12e^{\beta L_n},\qquad L_n\to\infty.$$

A bound `limsup log(1+max(S_n,0))/L_n < beta` on **that same family** would suffice.
An all-selectors theorem is a stronger optional target, not a logical necessity.
But an inverse-capacity bound without forcing and direct-complement control is
insufficient: a small inverse can multiply a growing forcing vector and leave
exactly the obstructed exponential rate. Aperture and physical-time scales
cannot be identified without the explicit adapter. [R4, R5, R8]

The **full-contact nullsource/exterior-energy subroute** is a distinct
construction; its source is not identified with the original detector above.
The continuous-contact dossiers supply exact exterior/range identities and
cumulative outgoing-energy lower laws. These create alternatives to a
pointwise upper. They do not yet provide a subexponential cumulative upper.
Projected compact-test forcing adapters already exist; rediscovering them does
not eliminate the full-aperture cost or direct term. [R5, R8]

**Open research target C:** independently control the full original-detector
Schur loss, or the exact complete cumulative outgoing energy in the relevant
native contact construction, with an exponent strictly below its proved lower.
Principal-minor or selected-shell estimates require a proved transport to this
object before they are usable.

### Path D — finite pole-neutral first-negative contact

This is a distinct finite boundary problem. The fixed seed lift
`T_a=D^2+aI`, `a=(L/(4 pi))^2`, maps the specified even/odd seed constraints into
the moving pole-neutral carriers. It is not an isometry; both the positive
metric and stiffness must be retained. The relevant contact includes both
parities, ties, inherited kernels, and prime seams. [R9]

With the whole kernel/complement splitting, the Schur germ is

$$F(t)=A(t)-B(t)C(t)^{-1}B(t)^*,\qquad F(0)=0,$$

On a `C^2` cell, with `C(0)>0` and the whole-kernel contact conditions
`A(0)=B(0)=0`, the first derivatives are
`F'(0)=A'(0)` and `F''(0)=A''(0)-2B'(0)C(0)^{-1}B'(0)^*`.
Positive semidefiniteness of the first derivative alone does not control exits
on its nullspace, where arbitrarily high odd-order exits remain possible.
Strict positive definiteness would give a local outgoing positive margin.
Prime seams require their own one-sided regularity and full outgoing germ;
these formulas do not assume two-sided differentiability across a seam.
An asserted finite Taylor order is not an exit theorem.

The archive contains two stronger negative findings that Round 2 must retain:

* A coherent positive modification of prime two produces a pole-neutral
  crossing while preserving the geometric and shape identities. It breaks the
  actual divisor identity, so it refutes a geometry-only argument, not a
  genuinely arithmetic one.
* A global metric-compatible positive-semidefinite transport remainder is
  already falsified for the actual native construction. The small-aperture
  identity `H=-log(L)G+J` makes
  `d/dL tr(G^{-1}H)=-(K-2)/L+O(L)<0`, whereas such a transport remainder would
  force a nonnegative trace. Even the archived `L H` repair has a native
  obstruction. This is not an untested proposal worth simply rerunning. [R9]

**Open research target D:** derive a new restriction from the unchanged native
arithmetic on the entire outgoing Schur germ, or a properly controlled
nonmetric source-dependent mechanism that excludes the generated first exit.
Putting the desired outgoing sign into a packet premise is not a proof.

## 5. What the external seven-eighths result can contribute

The exact pinned external source was fetched afresh in this investigation from
both the user's fork and the official repository. It declares

```lean
theorem OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re
    {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) : riemannZeta s ≠ 0
```

The ordinary Dirichlet L-function companion adds the principal-pole exclusion.
This is not an ordinate-bounded theorem or a renamed zeta object. The earlier
October 25 report contains a detailed historical source/compiled-axiom audit;
this turn verified the current pinned root source and its identity, but did not
recompile the external 2,924-module closure. It uses a different Lean/Mathlib
pin from the native repository. [R5, R10]

At that separately admitted authority level, reflection gives
`Theta <= 3/8`. This yields positive-damping native integrability for damping
strictly above `3/8`. It does not yield the boundary case, all positive damping,
or `Theta=0`. The external detector argument also has its own Hecke-family
uniformity and quantitative geometry. A native zeta rate equality is not an
improved uniform Hecke estimate and does not let the external proof iterate to
the critical line.

Round 2 should keep an optional, separately pinned external-transfer lane. It
must either provide the exact theorem and native adapter under compatible
formal evidence or label the composition as paper-level. The filtered finite
certificate below does not need the external seven-eighths theorem.

## 6. Executed closure attempts and their stopping points

| Attempt | What was used and checked | Result |
|---|---|---|
| Compose exact rate with completed-field decay | Literal source, high-mask correction history, residue-preserving balanced multiplier | The residual retains the original rate; no opposing upper |
| Iterate the external zero-free strip | Exact external root and archived quantitative detector geometry | Only `Theta<=3/8`; the improvement/iteration premise is absent |
| Extend the three-axis estimate to the full trace | Axis proof and source/twist identities | Complement and mixed terms remain unbounded at the required scale |
| Infer zero reality from positive spectral forms | Actual forced Euler/resolvent/sample identities | Equation remains forced; nonreal positive-Gram controls survive |
| Infer causal density from positive contraction | Actual completion and explicit equal-power twin kernels | Generic inference is false; arithmetic target information is essential |
| Optimize the first few raw dictionary columns | Actual delayed source, pulse separation, local divisor identity | Rigorous finite-size lower exceeds the proposed certificate threshold |
| Smooth with the fixed source-preserving filter | Exact multiplier factorization and transported witness | A finite low-height certificate succeeds; global convergence remains open |
| Pass to a bounded-input compactness limit | Actual boundary-zero/source-visibility obstruction | New undamped target is outside the exact range; successful inputs must grow |
| Repair profiles by finite quadratic self-duality | Earlier proof for arbitrary real symmetric finite coefficient matrices | Stated finite distinct-profile repair class is excluded; no claim for infinite or higher nonlinear families |
| Use metric-compatible positive transport | Original Path D deep note and trace identity | Already falsified on actual native source; not reopened |
| Infer Sturm structure from the native positive jump gain | Actual Archimedean density and unchanged prime-two atom | Fresh ordered negative minor, proved below; full resolvent/semigroup questions are separate |
| Use fixed finite derivative sign at a contact | Whole-kernel Schur germ and flat-exit controls | Higher-order/seam branches remain; no D-EXIT theorem |

This is a search for mathematical incompatibility. It does not claim to have
exhausted all possible proofs of RH. A route is rejected only for the stated
mechanism and source/domain class.

In particular, the inherited finite quadratic result uses the actual eligible
profile family at distinct spectral parameters `kappa`, after reflection
duplicates are removed and nonreal conjugate parameters are expressed through
their real blocks. For a real symmetric finite matrix `A`, Fourier self-duality
of the specified quadratic profile forces `A=0` in that class. Repeated-node
jets, infinite families and higher nonlinear repairs are outside this result.
This spectral parameter is distinct from the causal Laplace displacement
`lambda=rho-1/2`; the two coordinates must not be interchanged. [R5]

## 7. A verified finite output from the unchanged source

### 7.1 Why the raw small-dictionary programme must change

The earlier source-specific proof gives, for the residual
`r_x=v-sum x_n g_n` and local divisor discrepancies

$$d_k=\mathbf1_{k=1}-\sum_{n\mid k}x_n,$$

an isolated-pulse inequality through index 2047:

$$\|r_x\|_2^2\ge S^2\sum_{k\in\mathcal K}\frac{|d_k|^2}{k},\qquad
S^2\ge12e^{-1/512}2048^3.$$

If an isolated squarefree index `k` is omitted, Möbius inversion and weighted
Cauchy–Schwarz yield `||r_x||^2 >= S^2/sigma_1(k)`. With
`2047=23*89`, this proves **every initial-segment raw trial with N<=2046 has
residual norm greater than 6900**. The earlier prime-only example gives the
slightly smaller cutoff 2038 and a norm above 7000. The squarefree result is the
stronger support restriction and is retained here. It also applies to a
nonconsecutive dictionary omitting that early squarefree index, however many
late columns are added. [R5]

This bound is finite-scale. It does not imply nonclosure as `N->infinity`,
because the isolated-pulse argument changes once the pulses overlap. The
specified raw regional witness margin is at most `1/12`, so more precision or
a different optimizer cannot rescue these small raw dictionaries.

### 7.2 A fixed filter that retains the exact source

Use the actual causal probability translate `qPlus` and the stable filter

$$B(z)=\frac{z+3/2}{(z+1/2)^5},\quad
b(t)=\mathbf1_{t\ge0}e^{-t/2}\left(\frac{t^3}{6}+\frac{t^4}{24}\right),
\quad\|b\|_1=48.$$

Let `I(z)=(z-1/2)/(z+1/2)`, an isometry on the causal half-line, and

$$u_0(t)=\mathbf1_{t\ge0}e^{-t/2}(1-t),$$

$$h_0(t)=\mathbf1_{t\ge0}e^{-t/2}
\left[(1-t)\lfloor e^t\rfloor+\log(\lfloor e^t\rfloor!)\right].$$

Set `u=qPlus*u0`, `h=qPlus*h0`. The exact identities are

$$Bv=I^2u,\qquad Bw=I^2h.$$

The known common `I^2` is removed isometrically **on this proved range**.
Convolution by the unchanged `qPlus` is an `L2` contraction. Thus a comparison
residual for `u0,h0` provides a valid upper for the filtered actual-source
residual. No unbounded inverse of `B`, source replacement, truncated sinc
product or arbitrary division by an inner factor is used. [R5]

### 7.3 The rational four-column baseline

Take `x=(1,-1,-1,-2/3)`. The full-line unitary comparison maps its energy to the
classical fractional-part residual. The pole moment `sum x_n/n=0` makes that
residual vanish on `x>1`. On changing variables to `y=1/x`, the remaining step
function is

$$C(y)=1-\lfloor y\rfloor+\lfloor y/2\rfloor+\lfloor y/3\rfloor
+\tfrac23\lfloor y/4\rfloor.$$

Its period is 12, with values

$$ (1,0,0,0,2/3,-1/3,2/3,-1/3,1/3,1/3,1/3,-2/3). $$

Hence its energy is the positive series

$$E_0=\sum_{k\ge1}c_{k\bmod12}^2\left(\frac1k-\frac1{k+1}\right).$$

The squared period has mean `13/54`; its centered cumulative sums are at most
`41/54`. Integrating the first 47 cells and applying the periodic Abel tail
bound at 48 gives the exact rational upper

$$E_0\le\frac{315384568453197375401}{4648566756368995059600}
<\frac{17}{250}=0.068.$$

At a hypothetical zero with

$$\frac14\le\delta\le\frac38,\qquad1\le|\tau|\le2,$$

the correctly transported dual witness instead gives

$$\|B r_x\|_2^2\ge
\frac{8192}{93025}\left(\frac{2096767}{2097152}\right)^2
=\frac{4396431852289}{49942416588800}>0.08803.$$

These inequalities are incompatible. They certify the stated rectangle
`3/4<=Re(rho)<=7/8`, `1<=|Im(rho)|<=2`, with the reflected counterpart available
from the functional equation. It is an already-known zero-free low-height
region, used here as a native-channel acceptance baseline. [R5]

The rational arithmetic was independently reconstructed in this turn, including
the period, tail, source margin, a separate 4095-cell bound and the raw-source
obstruction. The attached `verify_round2_controls.py` passes without numerical
quadrature or a floating matrix inverse. Its receipt explicitly distinguishes
the finite arithmetic from the analytic operator proof and from Lean.

### 7.4 What still prevents global closure

The comparison optimization is the classical Nyman–Beurling problem. The
actual source-smoothed Gram is bounded through probability convolution; it is
not equal to the unconvolved classical Gram. The reduced Mellin kernel
`1+log x` also fails the regularity hypothesis of the general good-kernel
theorem at zero. The correct equivalence uses the original strong criterion
and the proved bounded adapters. The separate original compact-source probe
does satisfy the good-kernel hypotheses. [R5, P1]

There is still no independent all-`N` estimate driving the relevant residual
to zero. A finite certificate can exclude its own compact region without
solving that estimate. A long decreasing numerical sequence does not establish
an asymptotic limit.

## 8. Quantitative prefix and error-budget refinements

### 8.1 Prefix constraints are stronger than an unconstrained optimizer suggests

The earlier report already states coordinatewise convergence to the actual
Möbius coefficients. The following is a quantitative implementation refinement,
not a novelty claim for that observation.

Let `alpha` be the left endpoint of the essential support of `w`. On
`[0,alpha+log(M+1))`, all columns with index greater than `M` vanish. The exact
local identity `v=sum mu(n) g_n` therefore gives, for every trial with `N>=M`,

$$r_N=\sum_{n\le M}(\mu(n)-x_n)g_n\quad\text{on that interval}.$$

The finite prefix Gram on this interval is positive definite: take the earliest
nonzero coefficient and use positive `L2` mass arbitrarily close to the first
activation of its column, before the next column starts. Consequently

$$\|x_{1:M}-\mu_{1:M}\|_2^2
\le \frac{\|r_N\|_2^2}{\lambda_{\min}(G_M^{\mathrm{prefix}})}.$$

For the actual source `alpha=0` can be proved from the one-copy sinc product:
retain a finite product prefix with total omitted width less than any given
`h>0`. Its positive-real Laplace transform has a lower bound of the form
`C_K z^(3-K) exp(-sigma z/(K+1))` for `W(z)`. A supposed initial support gap
`h` would give `|W(z)|<=||w||_1 exp(-h z)`, a contradiction. A support-containment
theorem alone is not this exact endpoint proof. [R3]

Use the resulting finite prefix Gram for diagnostics and certified lower
bounds. Do not infer convergence merely because the optimized coefficients
look Möbius-like; raw Möbius truncations have their own obstruction.

### 8.2 A successful raw sequence requires growing input and adaptive cutoffs

The new undamped `v` is outside the exact range of `T`, although closure remains
the open criterion. At a source-visible critical zero of multiplicity `m`, the
earlier boundary-pole argument gives, in the small-error regime,

$$\|v-Tf\|_2\le\eta\quad\Longrightarrow\quad
\|f\|_2\ge(c_*/\eta)^{2m-1}.$$

This statement needs its explicit source-visible critical-zero evidence; it is
not assumed to be an already imported native Lean theorem. The detailed prior
proof gives multiple such evidence routes. [R5]

For a finite source input let

$$A_x=\sum_n|x_n|/\sqrt n,\qquad J_2=\|j\|_2.$$

Then `||f_x||<=J2 A_x`, so the certified **kernel-lag** cutoff error

$$\|(T-T^{[T]})f_x\|_2\le2e^{-T/2}J_2A_x$$

must follow the actual coefficient budget. Requiring that particular bound to
be at most `theta eta` entails

$$T\ge2\log\frac{2J_2A_x}{\theta\eta}
\ge4m\log(1/\eta)+O(1).$$

This is a requirement for the stated certificate bound, **not** a universal
lower bound on true truncation error or computational complexity. A final-output
time cutoff also has to account for delays. The horizon
`S>=T+log N+2sigma` covers the **lag-truncated trial output**, while the
noncompact target has the separate exact tail, for `S>=2sigma`,

$$\|\mathbf1_{[S,\infty)}v\|_2
=\frac{2}{\sqrt3}|J_+(-3/2)|e^{-3S/2}.$$

This tail must also enter the residual budget. A numerical source that does
not preserve the exact annihilating moments cannot reuse that exact formula
without its global source-error allowance. Absolute output time must not be
confused with kernel lag.

Likewise a source approximation with `L2` error `epsilon_j` has sufficient
combined error bound

$$\epsilon_j\bigl(\|c\|_1+\|a\|_1 A_x\bigr).$$

The allowed source error in this budget is of order at most `eta^(2m)` along a
successful raw sequence satisfying the inherited input lower bound. Fixing
precision and then increasing coefficients invalidates the old error bar.
The full derivation and its scope restrictions are included separately.

### 8.3 A changing filter can erase both signal and error

If `B_N=2^(-N)I`, every fixed residual has `||B_N r||->0`, including one separated
from the causal range. Its witness margin shrinks by the same factor. A
variable-filter programme must certify the error divided by the correctly
transported positive margin. The fixed filter in Section 7 avoids that
quantifier trap. This finite synthetic control is executed in the companion
checker; it is not a model of the full zeta construction.

## 9. Fresh source-native obstruction to the immediate TP2 shortcut

The new calculation concerns the **positive off-diagonal jump gain**, with the
literal native density and prime-power coefficients

$$\rho(t)=\frac{e^{-t/2}}{1-e^{-2t}},\qquad c_n=\frac{\Lambda(n)}{\sqrt n}.$$

Its off-diagonal measure is

$$d\mathcal K_R(x,y)=\rho(|x-y|)\,dx\,dy+
\sum_{2\le n\le e^R}c_n(d\nu_{\log n}+d\nu_{-\log n}),$$

where `nu_a(I x J)=|(I-a) intersect J|`. The measure is used only away from the
singular diagonal. It occurs with a minus sign in the full jump stiffness;
the full signed native form is a different object. [R11]

Put `a=log 2`, `d=1/10`, `h=1/1000`, `R>=1` and choose ordered row intervals

$$I_1=[a+d,a+d+h],\quad I_2=[a+2d,a+2d+h]$$

and ordered column intervals

$$J_1=[0,h],\quad J_2=[d,d+h].$$

All four lag intervals lie in `(1/2,1)`. Only the `(1,2)` rectangle meets a
prime-power atom, and that is the actual prime-two atom with overlap `h`.
Every smooth entry satisfies `h^2/2 < b_ij < 2h^2`, while
`c2=log(2)/sqrt(2)>1/3`. Thus the complete ordered matrix is

$$\begin{pmatrix}b_{11}&b_{12}+c_2h\\b_{21}&b_{22}\end{pmatrix},$$

and

$$\det<4h^4-\tfrac16h^3=-\frac{61}{375000000000}<0.$$

The exact source definitions, lag separation, atom normalization, sign and
determinant orientation were independently reviewed. Its rational budget
checker passes. The detailed proof is supplied as
`NATIVE_JUMP_ORDERED_MINOR.md`.

This excludes the immediate argument “the native positive gain is totally
positive, so it supplies Sturm-type crossing control.” It does **not** decide
total positivity for a separately defined full resolvent or heat semigroup;
it does not turn these rectangle tests into legal pole-neutral ground states;
and it proves neither native Weil negativity nor RH. The useful information is
the precise class of arguments that must now be changed or abandoned.

## 10. Revised Round 2 work specification

### 10.1 Preserve the inherited contracts

The original JSON is retained byte-for-byte under `inputs/`. The revision 2.1 JSON copies
all 25 original statements and proposed names. Their inherited acceptance flags
remain false; no new proof is claimed. Cross-references identify the later
deductions that affect their implementation order.

| Inherited IDs | Purpose | Revision 2.1 treatment |
|---|---|---|
| P01–P05 | Literal causal source, stable probe, transforms, zero separation, conditional sufficiency | Foundational; construct actual objects and domains before optimization |
| P06–P12 | Tail/correlation, target column, positive Gram, Schur error, innovations, spectral norm, conditional limit consumer | Keep; exact finite solver is research infrastructure, not the closing estimate |
| P13–P16 | Local Möbius inverse, divergent integer truncation, safe cutoff, zero barrier, noncausal leakage | Mandatory controls when their operation is used; no unqualified global integer sum |
| P17–P19 | Confluent zero witnesses, simultaneous lower bounds, primal certificates | Prefer the single-witness/primal certificate first; do not block on matrix inversion |
| P20–P23 | Correct classical adapter, product margin, regional certifier, certified source approximation | Keep original compact kernel distinct from filtered comparison; carry all error budgets |
| P24–P25 | Classical necessity and resulting iff | Optional true formalization/import; never add as project axioms |

### 10.2 Explicit proposed supporting amendments

These are proposed additions for review, not silent promotions into the frozen
PR294 contract or a claim of 17 new discoveries. The revision 2.1 JSON records exact
statements, source references, dependencies, forbidden substitutions and
acceptance fields.

| ID | Supporting amendment | Origin/status |
|---|---|---|
| S01 | Isolated-squarefree dictionary obstruction; exact activation endpoint; all-prefix quantitative Möbius constraint | Inherited finite obstruction and coordinatewise result; strengthened prefix formulation DERIVED here |
| S02 | Pole moments `P_N(1)->0`, `P_N'(1)->1` with bounded-functional error bounds | Earlier October 25 paper deduction |
| S03 | Completed-output Bernoulli tail and asymptotically free leading-tail neutrality | Earlier October 25 paper deduction |
| S04 | Literal stable filter, exact `I^2` factorization and valid range isometry | Earlier October 25 paper deduction |
| S05 | Full-line classical comparison with negative-time cancellation and unchanged `qPlus` contraction | Earlier October 25 paper deduction |
| S06 | Transported filtered witness and exact four-column regional baseline | Earlier paper proof; finite arithmetic independently rerun here |
| S07 | Exact undamped nonrange and multiplicity-aware input-cost lower bound | Earlier paper proof with explicitly separated critical-zero evidence |
| S08 | Coefficient-dependent source/lag/output budgets and variable-filter normalized margins | DERIVED implementation refinement here; no universal complexity claim |
| S09 | Finite quadratic Fourier-self-duality obstruction in the precise eligible profile class | Earlier October 25 proof; no infinite-family extension |
| S10 | Fixed-witness imaginary-direction positive test and error threshold | Attached deep search; no positivity-producing arithmetic approximant supplied |
| S11 | Exact positive-damping abscissa and equivalence audit of actual native closing cuts | Attached deep search and current rate theorems; boundary unclaimed |
| S12 | Equal-power positive causal twins and full-line/causal distinction | Attached deep-search control; explicitly synthetic |
| S13 | Native jump-gain ordered negative minor | Fresh DERIVED proof and exact rational budget check in this pass |
| S14 | Every convergent scalar normalization of CT1 has limit aT; order-zero limit is zero | Inherited paper consequence of current native limit/nonmeasure theorem |
| S15 | Fixed-aperture legal approximation with exact pole-neutral repair | Inherited paper composition; no effective cutoff or no-exit sign |
| S16 | Global fixed-filter native approximation implies RH | Conditional consumer; its approximation premise remains OPEN |
| S17 | Three adapted positive tests and four explicit phase-complete bumps | Inherited paper derivations; exact height, independence and cost scopes retained |

The optional **C2/C3/C4** extension records are separate from these 17 amendments.
C3 includes the explicit epsilon/window correction and normalized regularizer.
The existing sharp C1 and maximal actual-square repair theorems are reused.
The JSON also contains 25 scoped control records, 13 deferred/research
dispositions and a complete proposed-module manifest. See Section 15. [C1–C8]


### 10.3 Build order chosen for mathematical information

**Milestone 0 — pin and native identity.** Freeze the inspected tree, copy the
original proposals unchanged, and bind each reused declaration to its full
type/source hash. Keep the current-head aggregate and release status separate
from the available mathematical slice. No theorem count changes during this
step.

**Milestone 1 — establish the actual probe and its obstruction.** Implement
P01–P04 and the independently typed physical consumers. Check causal delay,
one-copy `Q`, removable pole, multiplicity and the distinction from the old
completed input. P05 is a conditional wrapper and must stay labelled as such.

**Milestone 2 — reproduce the finite filtered baseline.** Implement S04–S06
and the conditional global consumer S16. The direct baseline has no P19 dependency; P19 remains a later general certificate. Replay the exact rational certificate
and give a native theorem for the specified compact rectangle. This is a
demonstration that the pipeline can issue a sound output, not a global proof.
The revision explicitly removes the unnecessary S06-to-P19 dependency. The finite baseline does not require implementing a huge raw Gram matrix,
all multi-zero jets, or an interval inverse.

**Milestone 3 — install failure controls and calibrated budgets.** Add S01,
S07–S08 and the relevant truncation/leakage controls P13–P16. Freeze separate
kernel-lag and absolute-output cutoffs, coefficient budgets and transported
witnesses in the receipt. Reject the raw small-dictionary and moving-filter
false positives deliberately.

**Milestone 4 — study the actual asymptotic obstruction.** Complete P06–P12
and the source-correct finite certifier as useful. Seek an explicit coefficient
family with an independently proved residual bound, allowing the required
input growth, or an independent upper on the optimal remaining residual.
Ill-conditioning, monotone decrease and repeated finite successes are recorded
as observations, never as the terminal estimate. Optional P17–P18 and P24–P25
should be built only when they answer a concrete remaining question.

**Parallel mathematical lanes A/C/D.** Each lane must target the exact OPEN
statement in Section 4. Use the current rate, first-contact and source theories
as inputs. If a candidate bound only reproduces the same positive rate, or if
its decisive premise is the desired sign, reject it before a large Lean build.
The global target can close through one valid route; the specification does
not require solving all four.

### 10.4 Experiments with meaningful acceptance rules

| Experiment | Required output | Stop/reject condition |
|---|---|---|
| Filtered regional primal | Rational coefficients; exact/certified energy upper; transported regional lower; all source and domain identities | `upper >= lower` gives NO_CERTIFICATE, not a disproof of the criterion |
| Raw prefix diagnostic | Verified prefix Gram lower eigenvalue and discrepancy from exact Möbius coefficients | A proposed tiny residual contradicts its own prefix lower bound |
| Lag/source stability | One absolute error budget using actual coefficients and filter | Old error bar reused after coefficients, source or horizon changed |
| Complete high-mask estimate | Full signed tuple decomposition with masks, collisions and complement retained | Bound applies only to unit axes, an insufficient unsigned majorant or an inactive small-`T` toy corridor |
| Fixed-family Schur upper | Same produced family, original complement, exact aperture/time conversion | Forcing/direct term omitted, or upper exponent not below lower exponent |
| D exit candidate | Whole-kernel, both-parity native germ with seams and inherited kernels | Geometry-only argument also proves the known modified-prime control impossible |
| Native jump TP proposal | Exact definition of gain, stiffness, compression, resolvent or semigroup | Conflation with the explicitly negative ordered gain minor |

The fixed log-slack schedule itself becomes arithmetically huge before its
large-`T` lower-factor cutoff is nontrivial. A small brute-force pilot cannot
be sold as a test of the proved cofinal asymptotic regime. Symbolic identities
and analytically priced remainder estimates should precede large enumeration.

## 11. Proof and claim acceptance

Every new Lean claim needs a real compatible source build, independently stated
expected type, physical/native domain consumer, transitive standard-axiom
audit, and an exact source-pinned receipt. A copied signature-only check is not
independent review. No project axiom, `sorry`, changed toolchain, substituted
source or hidden desired conclusion is permitted.

The parent mathematics and original PR294 contracts remain frozen. Any change
to a mandatory statement, domain or dependency must be a visible versioned
amendment with a mathematical explanation. Supporting results do not inflate
the 100-root count. Optional classical transfers remain optional until their
full proofs are available.

A finite certificate's analytical theorem, rational/interval verifier and
source receipt have different roles. All three are needed for its claimed
scope. A finite verification says nothing about unbounded height unless a
separate covering or asymptotic theorem has been proved.

The status vocabulary is fixed:

* **PROVED:** exact existing statement with the stated formal/compiler evidence.
* **DERIVED:** a supplied mathematical argument, not newly Lean-compiled.
* **LEAD / HYPOTHESIS:** an idea or unproved construction to test.
* **EXPERIMENTAL SIGNAL:** bounded computation or numerical observation without
  the needed general theorem.
* **OPEN:** no established closing statement.

## 12. Post-green research assessment

### What became formally true

The current checked source preserves the exact 100-root OPICA slice and its
same-state, source-rate, signed-measure, forced-profile and truncation controls.
No Lean mathematics changed between the attachment pin and the inspected head.
The completed predecessor receipt has been independently inspected, while fresh current-head checks remain incomplete. This
investigation supplies no new compiled theorem.

### Workflow harvest

Every declared current-head job is listed with its execution status, scientific
scope, class, historical result and source URL in the companion harvest. Fresh scientific output was not reread for every new running job; that distinction is explicit. The
important preserved outcomes include successful frozen boxes, unresolved
contact/Schur targets, the altered-prime crossing, the signed-ray falsification
and the absence of eligible inherited contacts. Pending jobs are not passed by
association.

### What changed

The revised plan uses the actual finite obstruction to avoid an unproductive
small raw-dictionary build. It promotes the already derived filtered native
certificate to the first measurable milestone, adds all-prefix quantitative
diagnostics and adaptive error budgets, and excludes the immediate native
jump-gain TP2 shortcut. These are changes in the research/build specification,
not a claim that the terminal approximation theorem has appeared. Revision 2.1 additionally restores S14–S17, the corrected optional separator lane, source-specific controls, historical requirements and all deferred routes identified by the omission audit.

### Upstream implications

Keep the small source/causal probe abstraction separate from the global closure
premise. Source support containment must not stand in for the exact activation
endpoint. Kernel-lag cutoffs must not stand in for absolute output cutoffs.
Positive power data must not stand in for phase-sensitive causal range data.

### Downstream implications

The filtered verifier can produce rigorously scoped regional certificates.
The prefix and input-budget constraints can reject false numerical successes
before a proof campaign. The rate theorem tests any proposed arithmetic upper
against the correct zero displacement. Fixed-witness quantifiers can reduce
unnecessary uniformity demands in a genuine contradiction argument.

### Resurrected routes

Source-preserving causal approximation and fixed-witness comparison remain
worth pursuing with their exact new adapters. Paths dependent only on the
formerly missing native rate law can now be evaluated using it. Geometry-only
exit control, global metric-compatible PSD transport, equal-power positivity,
raw integer truncation and finite quadratic heat repair remain excluded in
their proved classes.

### New RH-relevant clues

The useful clues are the explicit mixed target column, complete retained rate,
the finite filter/witness baseline, quantitative early-coefficient rigidity and
the shrinking admissible class of contact mechanisms. They point toward an
arithmetic estimate retaining phase and the actual source. None is itself that
estimate.

### Falsification checks

Use the unchanged prime-two and altered-prime controls with their distinct
scopes, the forced Gram model, positive causal twins, raw finite-size barrier,
divergent integer completion, critical-zero input cost, variable-filter ratio
trap and high-order contact controls. Failures must remain in the ledger rather
than being hidden by a narrower test family.

### Highest-leverage next moves

First formalize and certify the actual filtered finite output and its compulsory
controls. In parallel, pursue one new **complete signed arithmetic estimate**
or **same-family outgoing-energy/germ restriction** that is not merely another
equivalent statement of RH. Require the candidate to survive the relevant
native and synthetic controls before expanding implementation. The global
closing estimate remains the research task.

## 13. Source guide

**R1.** `PR294_LIVE_HARVEST_2026-10-25.md`, `WORKFLOW_HARVEST.json`, exact source
and artifact receipts supplied in this package. Live PR and pinned tree:
<https://github.com/HMarcusWH/zeta-23-lean/tree/416aec21d4d6634675639b5397cc300d1f826e34>.

**R2.** `drive_archive_report.md`, `live_inventory.json`, `drive_reading_index.json`.
Live root: <https://drive.google.com/drive/folders/1FwRkN6sbJ4_Fhrqe53wpsJtByD2RXILb>.

**R3.** `history_math_audit.md`, the attachment coverage ledger, and the
quantitative prefix-support supplement in this package.

**R4.** Current native declarations:
[NativeWindowRate.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/416aec21d4d6634675639b5397cc300d1f826e34/Zeta23/OPICAFollowup/NativeWindowRate.lean),
[MovingSourceWindowRate.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/416aec21d4d6634675639b5397cc300d1f826e34/Zeta23/OPICAFollowup/MovingSourceWindowRate.lean),
[Consumers.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/416aec21d4d6634675639b5397cc300d1f826e34/Zeta23/OPICAFollowup/Consumers.lean),
[Step4OutputSufficiency.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/416aec21d4d6634675639b5397cc300d1f826e34/Zeta23/ExceptionalZero/Step4OutputSufficiency.lean).

**R5.** Earlier 25 October complete paper investigation, retrieved in full:
[Step4_Closure_Investigation_2026-10-25.html](https://chatgpt.com/library?file_id=libfile_c42a304601a081919008dc6eff538c57&account_id=personal).
Its proof records are inherited paper evidence, not newly compiled authority.

**R6.** `RH_Final_Gap_Residual_and_Handoff_Audit_2026-10-20`, exact Drive source
<https://drive.google.com/file/d/1eO_QNnwswL_VzTjIgbWGgk0MUQLYIiEW/view>.

**R7.** The three attached October 25 OPICA documents, preserved under `inputs/`:
deep search, Round 2 research/specification, and the original theorem contracts.

**R8.** `PRO_C_C05_Round4_Native_Exterior_Observability_2026-10-12`,
<https://drive.google.com/file/d/1Vg5dsSBQ3kum3LTfzTgX8E5WQ9B4wvw6/view>,
and the source-pinned original-detector complement/forcing modules linked by R1.

**R9.** `PATH_D_START_HERE_2026-10-14`, `ESET_PATH_D_DEEP_RESEARCH_NOTE_2026-10-14`,
the original finite pole-neutral contact investigation, and the transfer ledger;
exact IDs/hashes and reading disposition are in the Drive/attachment ledgers.

**R10.** Official external root source at its separate pin:
[OAI DirichletL/Nonvanishing.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean).
Source blob `46c67f4000906b1391a471d6e6396ac0da3c16a5`; historical compiler
evidence is reviewed in R5, Appendix 9. No fresh external build is claimed here.

**R11.** Native density/prime coefficients:
[Components.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/416aec21d4d6634675639b5397cc300d1f826e34/Zeta23/CCM/Components.lean),
and R8, Proof record J. Full new proof and rational receipt are included.

**P1.** L. Báez-Duarte, *A general strong Nyman–Beurling criterion for the
Riemann hypothesis* (2005), <https://arxiv.org/abs/math/0505453>.

**P2.** S. Bettin, J. B. Conrey and D. W. Farmer, *An optimal choice of Dirichlet
polynomials for the Nyman–Beurling criterion* (2012),
<https://arxiv.org/abs/1211.5191>. The optimal-rate statement is explicitly
conditional on RH and an additional inverse-derivative bound.

## 14. Reproduction

Run the two exact finite-control scripts with ordinary Python 3:

```text
python3 verify_round2_controls.py --output exact_control_receipt.json
python3 verify_native_jump_minor.py
```

The first verifies the inherited regional certificate arithmetic and the new
implementation controls. The second verifies the rational budgets in the
fresh native jump-minor proof. Neither command compiles Lean. The package
manifest binds the inspected source pin, inherited inputs, reports, contracts
and reproducible checks. Before a future proof build, refresh live PR/CI status
and compare mathematical source hashes; do not transplant a receipt across
changed source bytes.


## 15. Completeness revision 2.1

**25 October 2026.** This revision addresses the request to recheck the repository, project files and linked Drive folder for omissions from Round 2. **Step 4 and RH remain OPEN. New Lean declarations compiled in this investigation: 0.**

### 1. Audit outcome

The delivered v2 omitted useful mathematical consequences and did not give every inherited obligation an explicit destination. Revision **2.1** corrects those omissions while preserving the original 25 proposed contracts and the original 100 repository roots.

The revised specification now has **17 supporting amendments**, up from 13. The four added records are CT1 scalar-limit classification, the finite pole-neutral approximation composition, global sufficiency of the fixed filtered approximation, and phase-complete positive-test observability. These are proposed formalization records for existing paper deductions or compositions. Their addition is not a claim of four new discoveries or four newly compiled theorems.

The revision also carries the optional C2/C3/C4 programme, a control registry, the deferred source-specific research lanes, the original 49-requirement applicability crosswalk, WP0–WP7, the 100-root reuse map, and a complete proposed module map. Each audit finding has a concrete disposition in `disposition_matrix.json`. A DEFER entry preserves an unresolved obligation; it does not certify its conclusion.

The main report and JSON remain the authoritative current handoff. The exact delivered v2 is preserved under `round2_completeness/baseline_v2/`, and the three original OPICA inputs remain unchanged. No repository or Drive source was modified.

### 2. Evidence refreshed and its limits

#### Repository

The source pin is now **`416aec21d4d6634675639b5397cc300d1f826e34`**, tree **`0506bca8ffe613e9cd9ab844650a1141d4494f66`**, based on `d53dd70d38b0762af130b1d19b795af259f505f5`. Compared with the delivered `f5bafbc` pin, the change adds two workflow setup lines that install declared framework requirements and refreshes eight generated metadata files. **Lean sources and dependency pins are unchanged.** The comparison and source identity checks are included. [C1]

The completed predecessor aggregate was downloaded and inspected independently. Its recorded status is `COMPILER_VERIFIED_FULL_100`: 100 original roots, 28 acceptance units, 203 consumer queries, 83 required definitions and 18 constructors. All 4,780 source-manifest entries match the local predecessor checkout, including 1,353 Lean files. The three recorded successful command-log hashes, compiled exporter hash and 386 historical reviewed declaration-type hashes match. The receipt records 3,793 declarations using only the three standard axioms. This is inspection of the actual receipt and its bindings; Lean was not rerun. [C1]

That same receipt explicitly leaves `release_ready=false`, `full_release_accepted=false`, independent human review `NOT_ESTABLISHED`, and RH, Step 4 and the independent closing inequalities OPEN. The predecessor's generated-state gate failed because `cryptography` was absent; its summary failed the dependent gate. Its full100 and dependency-delta jobs succeeded. These distinct outcomes are preserved. [C1]

At **17:07:17 UTC / 18:07:17 Europe/Stockholm (CET)** on 25 October, the new head had 22 workflow runs and 76 declared jobs: **51 successful, 12 in progress, one skipped, and 12 not yet instantiated**. There were no current failures at that snapshot. The full current ledger retains every job, its run and event, and the distinction between current execution status and historical scientific output. Neither old success nor unchanged sources is represented as a completed fresh aggregate. [C1]

The reuse crosswalk accounts for **100/100 original roots** across 40 mathematical modules, including their frozen contract, declaration location, source hash, independent expected-type consumer and physical/domain consumer. All 42 historically reviewed exported source hashes still match. This avoids rebuilding old infrastructure under a new name while keeping exact theorem hypotheses visible. [C1]

#### Project files and Drive

All **40 direct project files** have explicit dispositions. Their inherited extraction ledger accounts for nested archives and duplicates; it does not claim a new semantic rereading of every embedded page. This pass read the original operating rules, the complete selected CT1, finite-neutral, iteration, Euler-product and positive-root arguments, the relevant historical build specification, the requirement register, and the specific older source adapters used by this revision. The project audit records proof review separately from acquisition and inherited review. [C2]

The Drive folder was recursively relisted at **16:57:17 UTC**: **1,206 unique files in 152 folders**, zero listing errors. Comparing IDs, title, size, modified time, MIME and file/folder kind found no additions, removals or selected metadata changes. This is a metadata comparison, not a byte-hash comparison of all 1,206 files. [C3]

The expanded pass fetched 16 source records: 13 read in full and three by exact section or schema. It also fully reread the post-green amendment, latest extracted B04 paper and Path D start, and reviewed the consolidated final paper's analytic/sampling/acceptance sections and C05's original exterior-closing section. The combined reading ledger has 22 records for this expanded pass. The original P0 manuscript, every R1/R2 proof page and the entire historical A/C archive were not reread end to end. The appropriate conclusion is that all material findings identified in this source-to-contract audit now have a disposition—not that every archived argument has been independently re-proved. [C2, C3]

### 3. Four restored supporting contracts

#### S14 — all scalar limits of the CT1 family

The native theorem already proves, on every Schwartz test,

\[
L^{-2}\nu_L\longrightarrow T,
\qquad
\nu_L=D_L+D_{-L}-2\cosh(L/2)D_0,
\qquad
T=\sum_{n\in\mathbb Z}(n^2\delta_n''-2n\delta_n').
\]

It also proves that $T\ne0$, that it is not of order zero near any nonzero integer, and that normalized local variation diverges. The missing Round 2 consequence is the full scalar classification:

\[
L_j\ne0,\ L_j\to0,\ c_j\nu_{L_j}\to U
\quad\Longrightarrow\quad
\exists a\in\mathbb C:\ c_jL_j^2\to a,\quad U=aT.
\]

Choose a Schwartz test \(\phi_0\) with \(T(\phi_0)\ne0\). The quotient

\[
c_jL_j^2=
\frac{c_j\nu_{L_j}(\phi_0)}{L_j^{-2}\nu_{L_j}(\phi_0)}
\]

converges to a scalar $a$. Apply the product limit on every other test to obtain $U=aT$. Consequently a limit that is locally of order zero on the real line, or on a neighborhood of any nonzero integer, must be zero. Order zero only near the origin would not be enough. No monotonicity of $L_j$, positivity of $c_j$, or common variation assumption is needed for this particular scalar classification. It says nothing about changed families, nonscalar transformations or added counterterms. [C2, C4]

The related controls are also explicit: for $0<L<\log2$, the native positive sinc mass is $2e^{-L/2}(1-e^{-L})$, its ratio to $L$ tends to 2, and its ratio to $L^2$ diverges. Sinc squared is not Schwartz, so its existing integrability argument must be retained. The near-gap atoms at \(\pm e^{-L}\) violate the exact unit gap. The separate synthetic sequence $n(\delta_{1/n}+\delta_{-1/n}-2\delta_0)$ shows why generic Schwartz convergence does not imply convergence on all continuous compact tests without common variation. The native controlled $C_c$ upgrade is already available with that premise. [C1, C4]

#### S15 — finite approximation with exact pole-neutral repair

The project has a paper composition that was not exposed as a Round 2 contract. Fix $L>0$, write $a=(L/(4\pi))^2$, and use the legal centered stencils

\[
e=(1,-4,6,-4,1),\qquad o=(-1,2,0,-2,1).
\]

For \(\ell_0(u)=\sum u_n/(a+n^2)\) and \(\ell_1(u)=\sum nu_n/(a+n^2)\), their constraint matrix is diagonal:

\[
\ell_0(e)=\frac{24}{a(a+1)(a+4)},\qquad
\ell_1(o)=\frac{-12}{(a+1)(a+4)},\qquad
\ell_1(e)=\ell_0(o)=0.
\]

After centered padding to a common cutoff, the correction

\[
\widetilde u=u-\frac{\ell_0(u)}{\ell_0(e)}e
                -\frac{\ell_1(u)}{\ell_1(o)}o
\]

is exactly legal and pole-neutral. The actual native odd witness is $De=2o$; its denominator must be scaled consistently. The physical exponential-moment adapter makes the correction coefficients tend to zero when legal approximants converge to a neutral compact target in \(\|f\|_1+\|f''\|_1\). WCONT then preserves a strict negative margin. [C2, C5]

The resulting existential producer is

\[
\neg RH\Longrightarrow
\exists L_0>0\ \forall L>L_0\ \exists K\ge3\ \exists u\ne0:
\quad u\text{ legal and neutral},\quad Q_{L,K}(u)<0.
\]

At least one parity component is negative after splitting. It is not a claim that both are negative or that strict even can be selected beforehand. This producer provides neither an effective cutoff nor a uniform aperture rate, the quantitative detector schedule, a selected-ground identity, or the outgoing first-boundary sign. Those remain separate obligations. [C2, C5]

#### S16 — the global consumer for the fixed filtered programme

The practical milestone already used

\[
B(z)=\frac{z+3/2}{(z+1/2)^5},\qquad
r_x=v-\sum_nx_ng_n.
\]

The terminal specification named only the raw residual. It now also states the sufficient filtered premise:

\[
\exists x^{(k)}\text{ finite}:\quad
\|Br_{x^{(k)}}\|_{L^2(0,\infty)}\to0
\quad\Longrightarrow\quad RH.
\]

Indeed, at an actual right zero \(\lambda=\rho-1/2\), with \(\delta=\Re\lambda>0\), every finite trial obeys

\[
\|Br_x\|_2\ge\sqrt{2\delta}\,|B(\lambda)V(\lambda)|>0.
\]

The dictionary vanishes at that evaluation, while the exact native source and fixed filter do not. This proof uses bounded causal Laplace evaluation. It requires no bounded inverse of $B$ and does not infer a raw norm estimate. The existence of a convergent filtered sequence remains OPEN. Raw and fixed-filter approximation are now explicitly alternative sufficient premises. [C2]

#### S17 — phase-complete positive observations

Three distinct statements must coexist:

| Construction | Exact scope | Missing ingredient |
|---|---|---|
| S10 fixed imaginary direction | One actual offcritical witness, every positive height | A native nonnegative observation of that fixed direction with sufficiently small error |
| Three adapted tests | One fixed independent actual Re/Im pair with nonreal \(\kappa=\rho(1-\rho)\); no height or simple-zero restriction | Effective test/recovery cost and a native positivity/comparison construction |
| Four explicit first-cell bumps | \(\gamma>2\pi/\log2\), with explicit points and margin | The same source-matched positivity/comparison construction |

For a fixed independent $n$-dimensional actual real zero-jet measure span, the existing positive-only-zero theorem and finite-dimensional cone separation give $n+1$ nonnegative smooth compact off-lattice tests realizing the covectors $e_1,\ldots,e_n,-\sum e_i$. Therefore every nonzero coefficient direction has a negative test pairing with a fixed norm margin. The actual canonical pair gives $n=2$, hence three adapted tests. This is an inherited paper consequence, not a separately compiled realization theorem. It has no uniform support, height, seminorm or recovery-cost bound. [C1, C6]

The four explicit construction retains its stronger height premise. With $q=\delta+i\gamma$, $Z=(1/4-q^2)/q$ and $u_j=j\pi/(2\gamma)$, the four values are $iZp_1,-Zp_2,-iZp_3,Zp_4$, where the positive $p_j$'s alternate the corresponding hyperbolic cosine and sine factors. Thus

\[
\min_j\Re(cg_\rho(e^{u_j}))\le-\eta_\rho|c|,
\qquad \eta_\rho=|Z|\min_jp_j/\sqrt2>0.
\]

The explicit derivative bound gives four nonnegative unit-mass bumps with a margin at least \(\eta_\rho|c|/2\). If actual nonnegative observations approximate these pairings and \(|c_T|\ge a_0>0\), their maximum error cannot be smaller than \(\eta_\rho a_0/2\). Obtaining those observations and beating that threshold is the open arithmetic task. Complex phase, finite Fourier parity and choice of source are not interchangeable. [C6, C7]

### 4. Optional separator work restored with corrections

**C1 is already available.** Reuse the sharp $2\operatorname{arsinh}(\|u-v\|/2)$ logarithmic norm comparison, scalar equality and positive-part companion in a seminormed additive commutative group. It needs neither an inner product nor completeness. It supplies no arithmetic upper on its own. [C1, C3]

**C2 remains an optional paper extension.** For a real signed Radon measure of polynomial total-variation growth, exact Fourier self-duality, zero restriction to \((-1,1)\setminus\{0\}\), and nonnegative off-integer restriction, prove that the measure equals its origin mass times the integer comb. This extends the old linear-growth/full-origin-gap interface. It must not accept generic tempered distributions containing atom derivatives. [C3, C8]

**C3 must use the corrected smoothing domain.** The full contract defines a real even nonnegative smooth compact probability regularizer \(\phi\), its autocorrelation \(\psi\), the triangle \(\Delta\), and

\[
f_\epsilon=\Delta*\psi,\quad
w_\epsilon=\operatorname{sinc}^2|\widehat\phi|^2,\quad
P_\epsilon-N_\epsilon
=D_\epsilon+\int f_\epsilon\,d\nu-\nu(\{0\}).
\]

The probability normalization is essential: $w_\epsilon(0)=1$. All pairings and the actual Jordan parts are part of the statement. The bound with smoothing cost \(\epsilon|\nu|([-2,2])\) requires **\(0<\epsilon\le1\)**. Otherwise enlarge that variation window to \([-1-\epsilon,1+\epsilon]\). The original unrestricted version has a repository counterexample at \(\epsilon=4\), which is retained with all seven original controls. [C3, C8]

The regional version retains $R\ge1$, $0<d\le1/2$ and \(\epsilon\le(2\pi R)^{-1}\), with coefficient \(d^2/(\pi^2R^2)\). A native application must separately construct the genuine order-zero source measure, prove an energy-to-observation inequality, and independently bound negative mass, tested Fourier defect, gap deficit, smoothing variation, the $b_T,c_T$ factors and any \(\pi^2R_T^2/d_T^2\) observation penalty. Its valid conclusion is \(\log(1+E_T)=o(T)\), not a literal equality $E_T=\exp(o(T))$. These native premises remain OPEN. [C3, C8]

**C4 is not missing square infrastructure.** The actual square no-repair theorem is already stronger than the old polynomial-growth proposal: it permits arbitrary locally finite complex lattice corrections with a tempered distribution agreeing on compact Schwartz tests, including addition of a selfdual tempered distribution. No total-variation-growth assumption is required. Reuse it. The generic fixed-measure C4 corollary can remain optional under all C2 hypotheses. Canceling one tested defect with a lattice atom is not full distributional self-duality. [C1, C3]

### 5. Failure controls and source identities restored

The revised control registry includes the following previously missing controls, with their proof or replay status:

- **Fixed-filter Euler products still diverge globally.** Actual finite prime-product dictionary trials agree with $Bv$ before the next-prime logarithm, yet for every fixed $0\le\epsilon<1/2$ their weighted norms have a lower growth bound of the form \(\exp(c_\epsilon P^{1/2-\epsilon}/\log P)\). Local exactness and this fixed filter do not rescue that sequence. Freely optimized coefficients remain a different question.
- **Correct Landweber descent can leave a residual.** The adjoint iteration converges to the target's projection onto \(\ker T_\epsilon^*\). The missing progress law or zero projection is an open input. The no-adjoint iteration has an inherited native frequency falsifier at frequency 12 for damping 0 and $1/100$; that enclosure was read, not rerun in this pass.
- **Forward positivity does not supply arbitrary positive convolution roots.** For the current triangular completion, the inverse Laplace measure of the logarithmic derivative contains the elementary density $e^{-t/2}+e^{-3t/2}-e^{t/2}$, which is negative on the atom-free interval \((\log2,\log3)\). The inherited argument excludes arbitrarily high positive roots of each fixed probability tilt. It makes no claim of an off-line zero.
- **Retain the original observation and continuation controls.** Coupled-Gram collision, raw-energy versus norm-first separation, history recovery cost, positive forced Gram at nonreal parameter, real/duplicate-node degeneracy, all affine histories, connected continuation, boundary-error equality and zero-radius failure remain explicit. The native jump minor and the metric-compatible transport falsification keep their exact scopes.

These controls are not new original roots. The register distinguishes existing native theorems, paper deductions, inherited numerical enclosures, and synthetic controls. Compiler rejection for a missing hypothesis is not described as a mathematical counterexample. [C1, C2]

The source crosswalk is now formula-level:

| Construction | Source and target | Valid transfer boundary |
|---|---|---|
| B02–B04 | $h=(D^2-1/4)^2(q*q)$, two copies of $Q$; target \(-R_{\mathrm{old}}H\zeta'\) | $h=q*j$ is a paper convolution adapter; a suitable upper transfers one way with the right horizon enlargement |
| October 13 triangle | One-copy $j$, target \(-RJ\zeta'\) | Rational normalization change can be causally invertible; it does not remove the \(\zeta'\) numerator |
| October 25 Round 2 | Literal delayed $j_+$; $V=RJ_+$, $W=RJ_+\zeta$ | New target needs its own physical identity and visibility proof |

Here $R_{\mathrm{old}}=(z-1/2)/[(z+1/2)(z+1)]$ and $R=(z-1/2)/[(z+1/2)(z+3/2)]$. The boundedly causally invertible multiplier $(z+1)/(z+3/2)$ changes both old operator and old input consistently; it does not equate different source problems. [C2]

### 6. Deferred lanes remain visible

The specification retains these as research options with exact source requirements:

| Lane | Missing task or constraint |
|---|---|
| Autocorrelation logarithmic-window covariance | Independently bound the full signed off-diagonal; retain the old two-copy source and one-way adapter |
| Fixed-frequency Suzuki orbit | Prove its actual local-work/subexponential upper; preserve the historical source and matched instability controls |
| Corrected prime-prefix OPEN-X | Bound the global residual subpolynomially with the exact escaping cutoff pulse and all prime powers |
| Forced-profile boundary amplitude | Supply an independent incompatible constraint on the actual \(\zeta(\rho)/b_\rho\); positive sampling alone is insufficient |
| C05 cardinal/exterior representer | Prove exact annihilation on the required superlinear set of distinct simple critical ordinates in the actual form domain |
| R002 and RES/TAIL/COFINAL | Preserve alternative quantifiers; block-level negative index is not global pair unmasking |
| Moving sextic OPEN-S | Optional alternative to the fixed two-factor rate route; not a new mandatory prerequisite |
| Finite-rank and growing-span recovery | Prove bounded recovery/common variation at the new scope; fixed finite-basis results do not provide uniform limits |
| Contact adapters and inverse estimates | Preserve same-state forcing, whole complement, endpoint/seam conditions and the missing trial excess |

The earlier $57/25$ unit-axis estimate still does not bound the full high observation. Its row-counting obstruction survives even if the individual constants become uniform; the full mixed/complement estimate remains missing. [C2, C3]

The stronger reported **Baiying Liu $0.874957019420\ldots$** benchmark is now recorded as **UNVERIFIED IN THIS INVESTIGATION**. The supplied primary manuscript and the old audit's explicit non-rebuild statement were traced. It does not replace X01's independently source-checked $7/8$ input. The similarly named October 11 `liu_scalar_*` receipts concern a compact-Weil scalar window and do not verify that half-plane claim. [C2, C3]

### 7. The 49 requirements and WP0–WP7

The complete crosswalk preserves each of the **49 original IDs**, its exact source paragraph, applicability and Round 2 destination. It is not a proof-of-discharge ledger. A successful route must complete the subgraph it uses; it need not solve every alternative. The historical 12 October “Track B” means first-negative-boundary propagation and maps mainly to today's C/D, not today's causal B. Both differ from the older CI Track A–D labels. [C2]

| Work package | Carry-forward disposition |
|---|---|
| WP0 | Refresh exact source and theorem authority; completed orientation is not restarted |
| WP1 | Reuse actual reciprocal-aperture concavity with its normalization and derivative premises when used |
| WP2 | Retain the K2 gap/gluing scope and explicit `hM51`; no all-cutoff or all-parity promotion |
| WP3 | Reuse strict-even adapters; keep odd/tie selected-ground requirements explicit |
| WP4 | **D2 Full remains deferred/open:** both K3 parity bottoms throughout \([1/512,\log16]\), with the small-aperture base below and every seam/normalization condition |
| WP5 | Preserve the originally prescribed modified-prime K2 crossing; later K3/Q14 or neutral controls do not silently replace it |
| WP6 | Preserve exact signed-correlation controls and the OPEN admissible signed upper |
| WP7 | Current integration, graph/registry and acceptance evidence remain separate from mathematical closure |

The archived guarded WP4 campaign has 30 verified layer payloads and 26 complete layers. The four unresolved even layers are Q9, Q13, Q14 and Q15, with 7, 7, 11 and 10 unresolved intervals respectively: **35 intervals total**. All 15 odd layers completed. The frozen SECOND feasibility check's 18/18 PASS is not this continuous full campaign. The FOURTH fallback applies after a frozen SECOND unresolved result, not as a tilewise substitution. `hWindows` remains an explicit premise, and no fresh full campaign was dispatched here. These retained engineering obligations do not block the independent finite filtered certificate. [C1, C3]

### 8. Implementation correction and validation

The standalone S06 four-column certificate depends on P04, S04 and S05 plus its finite periodic/Abel calculation. It does **not** require P19's general Gram chain. The unnecessary S06-to-P19 edge has been removed through an explicit revision record; P19 itself is unchanged. The exact finite baseline can therefore precede the general optimizer, inverse certificates and multi-zero machinery.

The proposed module manifest now covers every original contract, supporting amendment and optional extension. The core umbrella is separated from genuine optional classical imports; `ClassicalTransfer` may not be an axiomatic stub. The new modules for profiles, native cuts, synthetic controls, native jump controls, CT1 and finite neutral approximation are named rather than left implicit. The manifest is a proposed implementation plan, not a claim that those files already exist.

Validation checks the byte-for-byte preservation of the original contract array, deep equality of all inherited contract objects and metadata, unique IDs and names, source-reference resolution, alternative dependency groups, dependency acyclicity, module and milestone coverage, and false acceptance flags. The four terminal routes remain OPEN. Structural validation does not validate an analytic proof. The existing exact finite arithmetic scripts remain included and their unchanged receipts remain correctly identified.

The remaining mathematical work is still an independent source-specific estimate: a complete signed upper, an actual convergent raw or fixed-filter approximation, a source-matched Schur/energy upper, a valid positive-observation comparison, or an outgoing whole-kernel no-exit theorem. This audit makes those tasks and their prerequisites harder to omit; it does not supply the missing estimate.

### Sources and detailed ledgers

- **[C1]** `repo_omission_audit.md`, `repo_findings.json`, `repo_root_reuse_crosswalk.json`, `repo/current_workflow_harvest.json`, `repo/f5_aggregate_local_checks.json`, `repo/f5_dependency_delta_summary.json`, and `repo/historical_review_source_identity.json`. Current [PR294](https://github.com/HMarcusWH/zeta-23-lean/pull/294) and [pinned source tree](https://github.com/HMarcusWH/zeta-23-lean/tree/416aec21d4d6634675639b5397cc300d1f826e34).
- **[C2]** `project_omission_audit.md`, `project_findings.json`, and `project_requirements_49_crosswalk.json` / `.md`. Each source entry records the reviewed original path, hash, section and reading scope.
- **[C3]** `drive_omission_audit.md`, `drive_findings.json`, `drive_inventory_diff.json` and `drive_expanded_reading_ledger.json`; linked [Drive folder](https://drive.google.com/drive/folders/1FwRkN6sbJ4_Fhrqe53wpsJtByD2RXILb).
- **[C4]** [NearGapLimits.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/416aec21d4d6634675639b5397cc300d1f826e34/Zeta23/OPICAFollowup/NearGapLimits.lean), especially `dilation_normalized_limit_not_measure`, CT13Support and the controlled continuous-test extension.
- **[C5]** Original `RH_PoleNeutral_Contact_Investigation_2026-10-13.md` §§2.1–2.3, and current `CanonicalPoleNeutralCarrier.lean`, `CanonicalPoleNeutralPublicAPI.lean`, `BoundaryFlatApproximation.lean`, `NegativeWeilTestSupport.lean`, `FiniteNegativeObstruction.lean` and `BoundaryFlatFiniteWeil.lean`. Exact source locators and scaling caveats are in the project audit.
- **[C6]** Current [FiniteSpanSeparation.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/416aec21d4d6634675639b5397cc300d1f826e34/Zeta23/OPICAFollowup/FiniteSpanSeparation.lean) and the repository's `DERIVED_FINITE_POSITIVE_TEST_OBSERVABILITY_2026-10-24.md`, copied with this package.
- **[C7]** Unchanged input `OPICA_Proof_Directed_Deep_Search_2026-10-25(2).md`, §§7.1–7.4.
- **[C8]** [PostGreen amendment v1.1](https://drive.google.com/file/d/1m2eHS65c7pH4aF8qSJe9s8FowyzZIr_D/view), read together with the current repository's [POST_GREEN_RESEARCH.md](https://github.com/HMarcusWH/zeta-23-lean/blob/416aec21d4d6634675639b5397cc300d1f826e34/research/RHRC/integration/opica_followup/POST_GREEN_RESEARCH.md), including the explicit epsilon=4 counterexample and corrected consumer scope.
