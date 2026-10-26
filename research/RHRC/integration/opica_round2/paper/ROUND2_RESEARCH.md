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
