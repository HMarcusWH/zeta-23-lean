---
title: "OPICA: audited native preservation and follow-up paper"
subtitle: "Final consolidated paper package; end-to-end proof and evidence audit"
author: "Zeta23 research synthesis for Marcus Hermansson"
date: "21 October 2026"
fontsize: 10pt
papersize: a4
geometry: margin=22mm
colorlinks: true
linkcolor: blue
toc: true
toc-depth: 2
header-includes:
  - \usepackage{amsmath,amssymb,mathtools,booktabs,longtable,microtype}
  - \usepackage{xurl}
  - \usepackage{fancyhdr}
  - \pagestyle{fancy}
  - \fancyhf{}
  - \fancyhead[L]{\small OPICA / AUDITED FOLLOW-UP PAPER}
  - \fancyhead[R]{\small PAPER AUTHORITY / RH OPEN}
  - \fancyfoot[C]{\thepage}
  - \allowdisplaybreaks
  - \setlength{\emergencystretch}{3em}
---

# I. Completion statement and audit boundary

## I.1 What is finished

This release completes the **specified follow-up paper**: the eight Round 1 result/control groups, fifteen Round 2 statement families, their direct analytic dependencies, their native source identifications, and their scope limits are collected in one manuscript. The dependency on the fixed and slowly changing source window theorems is expanded in Part II rather than hidden behind their labels. Part III completes the actual arithmetic sampling term in the forced spectral construction: it is an explicit Stieltjes transform of the genuine critical-line zeta density, not a free boundary parameter.

The mathematical authority remains **DERIVED / PAPER, self-audited**. The full written argument is not an independent referee report or a new Lean proof. No repository write or CI run was performed. Nothing in this release promotes A-X, B-Y, C-Schur, OPEN-J46, D2/WP4, or RH to proved status.

The full OPICA research programme includes an independent exclusion of the hypothetical off-line obstruction. That objective is **not finished**. This release does not change the meaning of that objective in order to report success. It finishes a bounded, explicit mathematical deliverable suitable for formalization and independent review; it does not claim that arbitrary remaining research questions have been settled.

## I.2 Input identity and review coverage

The primary inputs are the complete OPICA construction, the complete Round 1 and Round 2 manuscripts, their theorem ledgers and contracts, the unchanged test scripts, and the original M0659, M1196 and DC/MS proof sources packaged with them. The supplied Round 1 and Round 2 archives were CRC-tested and every listed payload hash was recomputed. Earlier upload receipts were used only as historical byte-identity records, not as proof authority.

The prior Round 2 manifest itself says that the full programme was not completed and that no independent review had occurred [S2-manifest]. This finalization preserves that distinction. It does not repeat a claim to have read all 16,159 pages of the project archive during this audit. The complete supplied OPICA manuscripts and the named direct dependencies are the actual scope.

A fresh repository reference read returned main commit `97926d6a949fed7af0429a373b47abc772012834`; the fresh open-PR query returned an empty collection. These reads do not describe an unpublished worktree or establish that the separately assigned implementation has stopped. The final-head proof and workflow harvest must be performed when that head is available. No prior CI success was upgraded or replayed by the reads.

## I.3 Mathematical audit disposition

No counterexample to a substantive Round 1 or Round 2 conclusion was found in this audit. That is a statement about this review, not a certification that the papers are error-free. The following qualifications and proof details are made explicit throughout this consolidated release:

* Every general time-dependent mask is assumed measurable; the actual choice $B(t)=e^{\sqrt t}$ satisfies this. A bounded nonmeasurable function is not silently integrable.
* Every Laurent estimate uses a positive radius and a common meromorphic neighborhood of the closed contour, with only the stated central pole. The actual contour error bound is a separate premise.
* Measurement tolerances are nonnegative; recovery is extended from the finite-dimensional range by orthogonal projection before it is applied to noisy data.
* Palette variation is bounded in both mass and support delay. Source orders and inverse factor counts are fixed in the logarithmic-slack result.
* The native logarithmic-window theorem uses a supremum, not a rightmost zero. The vanishing lower moments, arbitrary multiplicity, top derivative and Laguerre factorial are retained.
* The co-Poisson construction is identified as an order-zero measure by local total-variation convergence. Its two divergent pieces are not transformed separately.
* The log-space lattice-minus-continuum force in Part III is defined first on compact tests and then by a derivative of an integrable sawtooth. Neither divergent exponential-growth term is independently assigned a Fourier transform on all Schwartz tests.
* Exact finite controls, numerical consistency, rendered pages, source hashes and theorem proofs have different evidentiary roles. Passing one does not imply the others.

The correction/coverage ledger gives a statement-by-statement disposition. These changes are not concealed edits to the frozen historical manuscripts. The originals remain in the evidence package, and the native choices used in the applications are unchanged.

## I.4 Integrated mathematical conclusion

There are now three distinct, fully described preservation mechanisms.

**Local analytic:** a named finite word of native source derivatives, delays, Euler factors, residual powers and completions transports the corrected pole to the stated nonzero residue or Taylor coefficient. Its correction ledger is part of the state.

**Global arithmetic:** the true inverse identity admits a fixed-order two-factor region of polynomial logarithmic width around $X^{1/2}$, with independently negligible Type I error. The actual low masks and norm-first comparison retain the complete observed rate. The final identification of that rate with $\Theta$ uses the explicitly audited source-window theorem below.

**Fourier/spectral:** the legitimate zero-generated measures and their jets have exact gap and duality but fail the required off-lattice positivity. The associated function satisfies a forced Euler equation. Its sampling values are now identified with a positive-measure Stieltjes transform. That calculation confirms, rather than removes, the force; it does not turn the function into an eigenvector of a homogeneous self-adjoint problem.

A closing theorem still needs an independent native restriction inconsistent with the surviving observation. The paper contains no such opposing theorem. The exact place where it would be consumed is identified without making it a premise of a theorem advertised as unconditional.

# II. The analytic rate bridge, checked through its dependencies

This part consolidates the full fixed-source argument of M0659/M1196 and the slow-source extension of DC/MS [S3--S5]. The statements are inherited paper mathematics, with the proof dependencies expanded and rechecked here. They are not counted again as newly discovered results.

## II.1 Native source hypotheses are established, not postulated

Use the one-copy source

$$
q=*_{n\ge1}\frac{\mathbf1_{[-c_n,c_n]}}{2c_n},\quad
c_n=\frac{s_0}{n(n+1)},\quad s_0=1/4096,
$$

$$
j_m=(\partial_t^2-1/4)^{m+2}q,\qquad
J_m(z)=(z^2-1/4)^{m+2}Q_0(z).
$$

The source, field, and measures have the meanings used in Parts IV--V. Every $j_m$ has the same compact support and the double elementary cancellation needed below. For a right zero $\rho=1/2+p$, $\Re p>0$, the entire box-product factor $Q_0(p)$ is nonzero: none of its individual factors vanishes off the imaginary axis, and on compact sets its tail differs from 1 by an absolutely summable $O(c_n^2|p|^2)$ sequence. Since $p\ne\pm1/2$, $J_m(p)\ne0$. This is also consistent with the pinned literal-source visibility theorem; no simplicity premise is used.

Gevrey bounds on the actual box convolution give fixed $A,D$ with

$$\|q^{(k)}\|_\infty\le AD^k(k!)^2.$$

Expansion of $(\partial_t^2-1/4)^{m+2}$ therefore gives, for $d=0,1,2$,

$$
\|j_m^{(d)}\|_1+\|j_m^{(d)}\|_\infty
\le \exp\{C(m+1)\log(m+2)\}. \tag{A1}
$$

All constants in this paragraph depend on the fixed source, not on the future horizon. One may majorize the finite expansion by a fixed multiple of $(D^2+1/4)^{m+2}D^d((2m+4+d)!)^2$.

For the actual integer drive, the continuum integral of

$$g_t(x)=(\log x)x^{-1/2}j_m(t-\log x)$$

is zero by $J_m(1/2)=J_m'(1/2)=0$. The first summation-by-parts remainder is at most $\int_0^\infty|g_t'(x)|dx$. Substitution $u=t-\log x$ gives

$$
|U_m(t)|\le C(1+t)e^{-t/2}
 (\|j_m\|_1+\|j_m'\|_1),\qquad t\ge0.
$$

The support stays away from $x=0$; the original causal gap is $g=\log2-s_0>0$. It follows that

$$\|U_m\|_2\le \exp\{C_1(m+1)\log(m+2)\}.\tag{A2}$$

This particular uniform bound does not need the optimized double-exponential localization theorem.

The standard compact-test explicit formula, initially derived from the actual transform $-J_m\zeta'/\zeta$, gives for $t>s_0$

$$
F_m(t)=-\sum_\rho \operatorname{mult}(\rho)
 J_m(\rho-1/2)e^{(\rho-1/2)t}
 -\sum_{n\ge1}J_m(-2n-1/2)e^{-(2n+1/2)t}.
$$

This is the classical explicit formula and zero-count input used by M0659; it is not inferred from OPICA algebra. The zero count $O(H\log H)$ and two integrations by parts on the fixed strip make the first sum absolutely convergent. The trivial-zero sum is uniformly bounded on $t\ge s_0+1$ by a geometric majorant; the remaining compact interval contains only finitely many native terms. Applying (A1) yields

$$
|F_m(t)|\le C_m e^{\Theta t},\qquad
\log(1+C_m)\le C_2(m+1)\log(m+2),\tag{A3}
$$

where $\Theta=\sup_\rho(\Re\rho-1/2)_+$. This prices the source constant; it does not set $\Theta$ to zero. A Lean implementation must import or prove the source-correct explicit formula and zero-count theorem, not replace them by an opaque assumption called `nativeRate`.

## II.2 Uniform auxiliary completions

For integer $k\ge1$, define

$$
r_k(z)=\frac{z-1/2}{\prod_{j=k+1}^{2k+2}(z+j+1/2)},\qquad
\alpha_k=k+1/2,
$$

$$
c_k(t)=\frac{\mathbf1_{t\ge0}e^{-(k+3/2)t}(1-e^{-t})^k}{(k+1)!}
 [(2k+3)e^{-t}-(k+2)],\qquad a_k=c_k*N.
$$

An integer-parameter beta integral proves $\widehat c_k=r_k$. There is no initial derivative term: $c_k=(\partial_t-1/2)b_k$, where $b_k(0)=0$ and

$$b_k(t)=\mathbf1_{t\ge0}\frac{e^{-(k+3/2)t}(1-e^{-t})^{k+1}}{(k+1)!}.$$

Put

$$
\phi_k(u)=-\frac{d}{du}\frac{u^{k+2}(1-u)^{k+1}}{(k+1)!}
\quad(0<u<1),
$$

extended by zero. Direct native summation gives $a_k(t)=x^{-1/2}\sum_{n\ge1}\phi_k(n/x)$ for $x=e^t$. Its integral is zero. The distributional derivative of order $k+1$ has precisely one endpoint atom of magnitude one; expansion of the polynomial bounds its total variation by $1+2^{3k+4}$. Thus

$$
|\widehat\phi_k(\xi)|\le(1+2^{3k+4})|\xi|^{-k-1},\qquad\xi\ne0.
$$

The periodized Fourier series is absolutely summable because $k+1\ge2$. Evaluating it at the actual real cutoff gives

$$
|a_k(t)|\le A_k e^{-\alpha_k t},\qquad
A_k=\frac{2\zeta(k+1)(1+2^{3k+4})}{(2\pi)^{k+1}}.\tag{A4}
$$

This derivation retains the endpoint atom and does not require positivity of $a_k$. Its actual Laplace transform is $r_k(z)\zeta(z+1/2)$ on $\Re z>-\alpha_k$, with the removable elementary singularity understood.

For every fixed nontrivial right coordinate $p$, direct denominator and factorial bounds give

$$
\|c_k\|_1\le\frac2{(k+1)!},\qquad
\frac{\|c_k\|_1}{|r_k(p)|}\le e^{C_p(k+1)},
$$

$$
\frac{|r_k(p)|}{A_k}\ge
 e^{-k\log(k+1)-C_p(k+1)}.\tag{A5}
$$

The constants in (A4)--(A5) are uniform in the completion index. They are established before choosing that index as a function of time. Source order $m$ and completion index $k$ are different parameters.

## II.3 All-multiplicity residual and terminal memory

Fix an actual right zero $\rho=1/2+p$ of multiplicity $d\ge1$, with $\delta=\Re p>0$. Let $y_{k,m}=c_k*U_m$. The genuine causal identity is

$$a_k*F_m=y_{k,m},\qquad \|y_{k,m}\|_2\le\|c_k\|_1\|U_m\|_2.$$

At $p$, the completion multiplier has order $d$ while

$$\widehat y_{k,m}(z)=-r_k(z)J_m(z)\zeta'(z+1/2)$$

has order $d-1$. The top moment is $(-1)^d r_k(p)J_m(p)\zeta^{(d)}(\rho)$; all lower relevant moments vanish. The derivative here is unnormalized: no extra $d!$ is inserted.

For $f_T=F_m\mathbf1_{[0,T]}$, the residual $y_{k,m}-a_k*f_T$ is an $L^2$ function supported in $[T,\infty)$. The exponential polynomials up to degree $d-1$ are adjoint-null for the convolution. The monic degree-$d-1$ shifted Laguerre polynomial times $e^{-\bar p t}$ has norm

$$e^{-\delta T}(d-1)!/(2\delta)^{d-1/2}$$

on that tail. Pairing with the residual retains just the top moment. Therefore

$$
\|y_{k,m}-a_k*f_T\|_2
\ge D_{\rho,m}|r_k(p)|e^{\delta T},\quad
D_{\rho,m}=\frac{(2\delta)^{d-1/2}|J_m(p)\zeta^{(d)}(\rho)|}{(d-1)!}>0.
$$

Writing $J_{\alpha,m}(T)=\int_0^T e^{-\alpha(T-s)}|F_m(s)|ds$, the tail bound (A4) gives the exact inequality

$$
J_{\alpha_k,m}(T)\ge\frac{\sqrt{2\alpha_k}}{A_k}
 [D_{\rho,m}|r_k(p)|e^{\delta T}-\|y_{k,m}\|_2]_+.\tag{A6}
$$

No global $L^2$ membership of $F_m$ was assumed. Only its finite truncation and the actually stable completed input were used.

## II.4 Fixed and slowly changing source window theorem

Let $T_i\to\infty$, $m_i\ge0$ integer and

$$m_i\log(m_i+2)=o(T_i).\tag{A7}$$

Then for each fixed $C>1$,

$$
\boxed{
\lim_i\frac{\log(1+\int_{T_i-C\log T_i}^{T_i}|F_{m_i}(t)|^2dt)}{2T_i}
=\Theta.}
\tag{A8}
$$

The fixed-source theorem is the special case of constant $m_i$ and arbitrary cofinal horizons. For clarity, the argument proves the full continuous fixed-source limit as well.

**Proof.** The upper bound follows from (A3) and (A7). At $\Theta=0$, nonnegativity of the logarithm supplies the other inequality. Suppose $\Theta>0$ and fix $0<b<\Theta$. Choose one actual zero with

$$\delta>\frac{\Theta+(C-1)b}{C},$$

then choose $\xi$ satisfying

$$\frac{\Theta-\delta}{C-1}<\xi<\delta-b.$$

This selection uses a supremum, not an attained maximum. Set $k_i=\max(1,\lfloor\xi T_i/\log T_i\rfloor)$. By the literal transform,

$$J_{m_i}(p)=(p^2-1/4)^{m_i}J_0(p),$$

so both signs of $\log|J_{m_i}(p)|$ have magnitude $O_p(m_i+1)=o(T_i)$. Equations (A2), (A5) make the subtracted input in (A6) exponentially smaller than its leading term. Since $k_i\log(k_i+1)/T_i\to\xi$, (A6) gives

$$\liminf_i T_i^{-1}\log J_{\alpha_{k_i},m_i}(T_i)\ge\delta-\xi.$$

The part of this memory before the terminal window is at most

$$
\frac{C_{m_i}}{\alpha_{k_i}+\Theta}
 e^{\Theta T_i-(\alpha_{k_i}+\Theta)C\log T_i}.
$$

Its upper rate is $\Theta-C\xi<\delta-\xi$, so it is negligible. Cauchy--Schwarz on the remaining window gives

$$
(J^{\rm win}_{\alpha_{k_i},m_i}(T_i))^2
\le\frac1{2\alpha_{k_i}}
\int_{T_i-C\log T_i}^{T_i}|F_{m_i}|^2.
$$

The lower rate is therefore at least $\delta-\xi>b$. Let $b\uparrow\Theta$. The selected zero, its multiplicity, and $\xi$ were fixed before each horizon limit. This proves (A8). $\square$

A changing Euler palette is not hidden in (A8): exact compensation leaves $F_m$ unchanged, while estimates on an expansion separately pay the palette mass and delay. The fixed-order logarithmic-slack application in R2-Q3 does not need moving $m_i$ at all.

## II.5 Closing implication and what it actually requires

For the R2-Q3 two-factor choice $r=2,m=1,C=2,Q=1,K=8$, norm-first comparison and the true low masks give a retained observation with rate $\Theta$. A zero-rate upper on that complete observation along a cofinal sequence would force $\Theta=0$ by (A8), and reflection would give RH. This implication is valid but its upper premise has **not** been established.

If $\Theta=0$ were independently established, (A3) for $m=0$ would make the literal $X_j$ bounded and hence belong to every positively damped $L^2$ space. No same-window Green inverse is used in this chain. The exact open input remains the signed upper or another incompatible native constraint, not the return notation.

# III. Completion of the actual spectral sampling term

This part is new to this finalization. Its proofs use the actual lattice-minus-continuum force of R2-S1, not an arbitrary synthetic forcing. Its purpose is to finish that native representation and test whether it yields an independent exclusion. It does not establish such an exclusion.

## III.1 Theorem F1: a tempered force with an exact Mellin transform

On $t\in\mathbb R$, define the real sawtooth weight

$$w(t)=e^{-t/2}\{e^t\}.$$

For $t<0$, $w(t)=e^{t/2}$; for $t\ge0$, $|w(t)|\le e^{-t/2}$. Thus $w\in L^1\cap L^2$. Define the tempered distribution

$$\mathfrak g=-(\partial_t+1/2)w.$$

On compactly supported tests its exact arithmetic form is

$$\mathfrak g=N-e^{t/2}dt.\tag{F1.1}$$

The right side is interpreted as a difference on compact tests, then by the left side on Schwartz tests. Neither exponentially growing summand is separately transformed as a tempered distribution.

Use the logarithmic Fourier convention $\mathcal F_{\log}f(\xi)=\int f(t)e^{-i\xi t}dt$, with Plancherel factor $1/(2\pi)$. Then

$$
\boxed{
\mathcal F_{\log}w(\xi)=-\frac{\zeta(1/2+i\xi)}{1/2+i\xi},
\qquad \mathcal F_{\log}\mathfrak g(\xi)=\zeta(1/2+i\xi).
}
\tag{F1.2}
$$

**Proof.** Between integer-log points, $w=e^{t/2}-\lfloor e^t\rfloor e^{-t/2}$, so $w'+w/2=e^{t/2}$. Its jump at $t=\log n$ is $-n^{-1/2}$, proving (F1.1), including $n=1$.

For $0<\Re s<1$, the absolutely convergent integral of $\{x\}x^{-s-1}$ satisfies

$$\int_0^\infty\{x\}x^{-s-1}dx=-\zeta(s)/s.\tag{F1.3}$$

Indeed, for integer $L\ge1$, direct integration by parts of the step function gives

$$s\int_0^L\{x\}x^{-s-1}dx=\frac{L^{1-s}}{1-s}-\sum_{n\le L}n^{-s}.$$

The sum-minus-integral limit is $\zeta(s)$ by the same elementary continuation used in CP1, and the tail integral is absolutely convergent in the stated strip. Substitute $x=e^t$, $s=1/2+i\xi$. Fourier transformation of the distributional derivative gives the second identity. $\square$

Put $a(\xi)=\xi^2+1/4$. Plancherel immediately gives the finite, exact source budget

$$
\boxed{
\frac1{2\pi}\int_{\mathbb R}\frac{|\zeta(1/2+i\xi)|^2}{a(\xi)}d\xi
=\|w\|_2^2=\log(2\pi)-\gamma_{\!E}.}
\tag{F1.4}
$$

For completeness, the last constant follows without an asymptotic guess. At an integer $L$,

$$
\int_0^L\frac{\{x\}^2}{x^2}dx
=2L-H_L-2(L-1)\log L+2\log\Gamma(L).
$$

Sum the exact cell integrals $1+n/(n+1)-2n\log(1+1/n)$, including the initial cell integral 1, to obtain this identity. Stirling and $H_L-\log L\to\gamma_E$ give the limit. This is a classical weighted zeta moment derived here in the required normalization, not a general novelty claim. In particular $\mathfrak g\in H^{-1}(\mathbb R)$.

## III.2 Theorem F2: actual sampling is a Stieltjes transform

Let $h_\kappa$ be an actual zero profile from R2-S1, and set

$$\psi_\kappa(t)=e^{t/2}h_\kappa(e^t).$$

The previously proved bounds imply $\psi_\kappa\in H^1(\mathbb R)\cap L^1(\mathbb R)$. Under this unitary log-coordinate map, the forced Euler equation becomes

$$
(-\partial_t^2+1/4-\kappa)\psi_\kappa=\kappa\mathfrak g.
\tag{F2.1}
$$

For a hypothetical off-line zero, $\Im\kappa\ne0$, because the zero is nonreal and $\Im[\rho(1-\rho)]=(1-2\Re\rho)\Im\rho$. Fourier transformation and the absence of a real multiplier zero give the unique $H^1$ solution

$$
\boxed{
\widehat\psi_\kappa(\xi)=
\frac{\kappa\zeta(1/2+i\xi)}{a(\xi)-\kappa}.}
\tag{F2.2}
$$

Define the positive spectral measure

$$d\omega(\xi)=\frac1{2\pi}|\zeta(1/2+i\xi)|^2d\xi.$$

It has finite $\int a^{-1}d\omega$ by (F1.4), although its unweighted total mass need not be finite. For $\kappa\notin[1/4,\infty)$ define

$$M(\kappa)=\int_{\mathbb R}\frac{d\omega(\xi)}{a(\xi)-\kappa}.$$

The integral is locally absolutely convergent in this parameter domain and locally holomorphic. The actual sampling value is

$$
\boxed{
b_\kappa=\sum_{n\ge1}h_\kappa(n)-\frac12
=\kappa M(\kappa).}
\tag{F2.3}
$$

**Proof.** The log-coordinate conjugation sends $-\partial_x(x^2\partial_x)$ to $-\partial_t^2+1/4$ and the compact-test force $\sum\delta_n-dx$ to $\mathfrak g$. Equation (F2.2) follows in distributions. The quotient is in $H^1$ because $a^2/|a-\kappa|^2$ is bounded on the real spectral range and (F1.4) holds; uniqueness follows by multiplying the Fourier transform of a difference by $a-\kappa$.

The actual sum and integral in $b_\kappa$ converge. Summation by parts, with the vanishing endpoint terms supplied by R2-S1, gives

$$b_\kappa=\int_0^\infty\{x\}h_\kappa'(x)dx
=\int_{\mathbb R}w(t)(\psi_\kappa'(t)-\psi_\kappa(t)/2)dt.$$

The latter is a continuous $H^{-1},H^1$ pairing; it is not evaluation of an inadmissible infinite sum on a generic $L^2$ vector. Plancherel and (F1.2)--(F2.2) give (F2.3). Absolute convergence follows from $\int a^{-1}d\omega<\infty$ and boundedness of $a/|a-\kappa|$. $\square$

In particular, with $\kappa=u+iv$, $v\ne0$,

$$
\frac{\Im M(\kappa)}{v}
=\int\frac{d\omega}{(a-u)^2+v^2}>0,
$$

$$
\|h_\kappa\|_{L^2(0,\infty)}^2
=|\kappa|^2\int\frac{d\omega}{|a-\kappa|^2},\qquad
\int_0^\infty x^2|h_\kappa'|^2dx
=|\kappa|^2\int\frac{a\,d\omega}{|a-\kappa|^2}.
\tag{F2.4}
$$

For two actual profiles the mixed versions reproduce R2-S2 exactly. These are not new conflicting evaluations of that identity; they identify its previously implicit source measure.

The independent source budget (F1.4) gives the valid, but not RH-closing, upper

$$
|b_\kappa|\le
|\kappa|\left(1+\frac{|\kappa|}{|v|}\right)
[\log(2\pi)-\gamma_E].\tag{F2.5}
$$

It also gives $\Im b_\kappa/v>0$. Thus attempting to prove that these samples are real at a nonreal parameter would contradict their own resolvent formula unless additional native information first excludes that parameter. Positive spectral density alone does not make $\kappa$ real.

At an actual critical-line zero the denominator can vanish at $\xi=\pm\Im\rho$. The numerator vanishes there with the actual zero multiplicity, and the norm/sample formulas can be interpreted by these removable almost-everywhere quotients. No generic principal-value boundary claim is needed or asserted in this release; the off-line application uses $v\ne0$ throughout.

## III.3 Theorem F3: exact boundary coefficient and the absence of a hidden eigenvalue argument

Take an arbitrary parameter $1/2<\Re\rho<1$ with $\Im\rho\ne0$, not necessarily a zero. Put $\kappa=\rho(1-\rho)$ and $b_\rho=(1-2\rho)/\kappa$. The unique log-form solution of (F2.1) has the physical expression

$$
\boxed{
\widetilde h_\rho(x)=1-\frac{S_\rho(x)}{b_\rho}
-\frac{\zeta(\rho)}{b_\rho}x^{\rho-1},\qquad x>0.}
\tag{F3.1}
$$

Here $S_\rho$ is the exact finite-sum function from CP1, not a continued Dirichlet series.

**Proof.** The finite-cell Euler equation and the integer jumps are valid for arbitrary parameters in this strip. The extra power solves the homogeneous cell equation and is globally smooth on $(0,\infty)$, so it changes none of the forcing atoms. Near zero,

$$\widetilde h_\rho(x)=1-\frac{\zeta(\rho)}{b_\rho}x^{\rho-1}.$$

This lies in the log form domain because $\Re\rho>1/2$. Finite-sum Euler--Maclaurin at infinity gives

$$
\widetilde h_\rho(x)
=-\frac{\zeta(1-\rho)}{b_\rho}x^{-\rho}
+\frac{\kappa}{2x^2}B_2(\{x\})+O_\rho(x^{-3}).
$$

Its derivative has the corresponding decaying homogeneous term and an $O_\rho(x^{-2})$ periodic part, so it also lies in the form domain at infinity. Thus it is the unique solution already identified in (F2.2). $\square$

The exact plateau condition on $(0,1)$ is now

$$
\widetilde h_\rho\equiv1\text{ on }(0,1)
\quad\Longleftrightarrow\quad\zeta(\rho)=0.\tag{F3.2}
$$

This is a diagnostic identity, not a proposed new RH-equivalent campaign. It locates precisely what a putative homogeneous spectral proof would need to rule out: the vanishing of a boundary-amplitude functional, not the existence of a nonreal forced resolvent. For an actual off-line zero the power term vanishes, and (F3.1) becomes the R2 profile. For generic parameters it does not vanish; the profile is not a positive sharp-gap defect and need not be $L^1$ in the physical variable.

The forcing spectral measure in F2 is genuine and explicitly known. It has **not** supplied a sign, monotonicity or incompatibility forcing the coefficient in (F3.2) to be nonzero. The new completion removes an unspecified sampling object from the representation, but does not turn the representation into a contradiction.

## III.4 Research consequence of the completed sampling calculation

The strongest defensible result is not “the spectral route is impossible.” It is that the native forced equation, the multi-zero Gram relations, the spectral moment, and the plateau all fit one exact model. Nonreal resolvents are allowed by its positive form. The missing exclusion cannot be obtained by simply discarding the forcing or renaming its sample sum.

An independent inequality on the actual boundary functional could still matter. No such inequality is proved here. Similarly, a new signed bound in the fixed two-factor arithmetic region could still close Step 4. The preservation and preparation theorems neither prove nor prohibit that mathematical input.


# IV. Round 1 complete technical proofs

The following chapters preserve the complete Round 1 technical arguments. Their local citation keys are resolved in the source register at the end of this part. The standing measurability and analytic-domain qualifications in Part I apply to generic formulations; all original native choices remain unchanged.

## R1 2. Literal source and notation

Keep

$$
s_0=1/4096,\qquad P=\partial_t^2-\tfrac14,
\qquad j=P^2q,
$$

where the original even compact probability density is the prescribed infinite box convolution. Its Laplace transform is

$$
J(z)=(z^2-\tfrac14)^2Q_0(z).
$$

There is one copy of $Q_0$ here. The distinct autocorrelation source $k*k=q*j$ must not be substituted for $j$. The original-source module proves nonvanishing of $J(\rho-1/2)$ at an actual off-line zero, without a simplicity premise. [R3]

Use the genuine causal arithmetic measures

$$
N=\sum_{n\ge1}n^{-1/2}\delta_{\log n},\quad
M_\mu=\sum_{n\ge1}\mu(n)n^{-1/2}\delta_{\log n},\quad
\Pi=\sum_{n\ge2}\Lambda(n)n^{-1/2}\delta_{\log n}.
$$

Their locally finite identities are

$$
M_\mu*N=\delta_0,\qquad N*\Pi=tN,
\qquad U_j=(tN)*j,\qquad X_j=\Pi*j=M_\mu*U_j.
$$

Prime powers and repeated factors are retained. The field and its source derivatives have a positive initial causal gap. [R5, S2]

Write

$$
Z(z)=\zeta(z+\tfrac12),\qquad
r_c(z)=\frac{z-1/2}{(z+1/2)(z+3/2)},
$$

and let $\mathfrak a=c*N$ be the actual completion, with

$$
c(t)=(-e^{-t/2}+2e^{-3t/2})\mathbf1_{t\ge0}.
$$

On the initial safe half-plane $\Re z>1/2$,

$$
\widehat X_j=-JZ'/Z,\qquad
\widehat{\mathfrak a}=r_cZ,\qquad
\widehat Y_j=-r_cJZ',\qquad Y_j=c*U_j.
$$

Continuation is used only after the actual transform identity has been established. A meromorphic continuation value is not a convergent integral outside its convergence domain. [R2, S2]

For a hypothetical right zero $\rho$, put

$$
\lambda=\rho-\tfrac12,\quad \delta=\Re\lambda>0,\quad
m=\operatorname{mult}(\rho)\ge1,\quad x=z-\lambda.
$$

Then $Z=x^mv$, $v(\lambda)=\zeta^{(m)}(\rho)/m!\ne0$, and

$$
\widehat X_j=\frac{-mJ(\lambda)}x+\text{holomorphic germ}.
$$

Source derivative order, inverse-factor count, zero multiplicity, and completion count remain different parameters.

For the energy discussion define

$$
\Theta=\sup_{\rho\ \mathrm{nontrivial\ zero}}(\Re\rho-1/2)_+,
\qquad I_C(T)=[T-C\log T,T],\quad C>1.
$$

The source-correct J5.2 paper statement identifies
$\log(1+\int_{I_C(T)}|X_j|^2)/(2T)\to\Theta$ for this fixed source and each fixed $C>1$. The initial endpoint is nonnegative for all sufficiently large $T$. MS1 treats its specified higher-source family only with the additional moving-order condition $d_n\log(d_n+2)=o(T_n)$ and quantitative source/completion estimates. These are inherited PAPER inputs, not consequences of the new elementary rate comparison. No zero attaining $\Theta$ is required. [S3, S5, S6]

---

## R1 3. NB1 — A concrete finite native preservation theorem

### 3.1 Explicit generators

Consider finite words made from the following operations on the actual causal seed, with each transformed source/field retained as a separately identified object.

| Generator | Transform multiplier | Native identity and scope |
|---|---|---|
| Apply $P^d$ to the compact source, $d\ge0$ | $(z^2-1/4)^d$ | Compact-source integration by parts and the initial causal gap remove initial jets; this is a specified source change. |
| Delay by $\tau\ge0$ | $e^{-\tau z}$ | Actual causal translation. |
| Finite Euler filter | $E_Q(z)=\prod_{p\mid Q}(1-p^{-z-1/2})$ | Convolution by the exact finite palette measure. |
| Inverse finite Euler filter | $E_Q^{-1}$ | Positive locally finite measure on integers supported on the finite prime set; transform absolutely convergent for $\Re z>-1/2$. |
| Rational causal filter and its inverse | $(z+a)/(z+b)$, $a,b>0$ | $\delta_0+(a-b)e^{-bt}\mathbf1_{t\ge0}dt$, with the analogous inverse. Both finite-variation causal measures. |
| Finite truncated-inverse residual power | $(1-Zm_Y)^r$, $r\ge0$ | $m_Y(z)=\sum_{n\le Y}\mu(n)n^{-z-1/2}$; convolution by a finite power of $\delta_0-N*M_{\mu,\le Y}$. |
| Current native completion | $r_cZ$ | Convolution by the actual $\mathfrak a$. |

When differentiation follows an added history, it is distributional differentiation of the zero-extended causal state; its endpoint distributions remain in the state/correction. No endpoint-free classical differentiation formula is asserted for an arbitrary new history.

Finite residual convolutions are well-defined locally on causal fields. Their use here does **not** assert that they are bounded operators on every weighted $L^2$ space. The transform identities start in the safe half-plane and give the relevant meromorphic germs by continuation.

The finite palette compensation identity is also exact:

$$
M_Q*(D_Q*U_j)=X_j,
\qquad
M_Q=\sum_{(n,Q)=1}\mu(n)n^{-1/2}\delta_{\log n}.
$$

It is a change of arithmetic expansion, not an unpriced change of the observed field. Neither this identity nor the scalar filter identities preserve a chosen gcd pair mask automatically.

At $\lambda$, all the listed factors except the explicit $Z$ in a completion are units. Indeed $\lambda\ne\pm1/2$, exponentials never vanish, $|p^{-\rho}|<1$, rational roots/poles are in the left half-plane, and $1-Z(\lambda)m_Y(\lambda)=1$. Also $r_c(\lambda)\ne0$ for a nontrivial right zero.

### 3.2 Statement and proof

Allow explicitly identified analytic additions $B_i$, such as established compact initial-history transforms. Write

$$
f_{i+1}=M_if_i+B_i,\qquad f_0=\widehat X_j,
\qquad C_0=0,\quad C_{i+1}=M_iC_i+B_i.
$$

If the word contains $p$ completion factors, then

$$
\boxed{f_n-C_n=U(z)Z(z)^pf_0(z),\qquad U(\lambda)\ne0,}
\tag{NB1.1}
$$

where $U$ is the product of the explicit unit factors listed above, including the rational part of each completion. Consequently

$$
\boxed{
\operatorname{ord}_\lambda(f_n-C_n)=pm-1,\qquad
\operatorname{lead}_\lambda(f_n-C_n)
=-mJ(\lambda)U(\lambda)v(\lambda)^p\ne0.
}
\tag{NB1.2}
$$

For $p=0$ this is a residue statement. For $p\ge1$, the analytic representative has first nonzero derivative

$$
(f_n-C_n)^{(pm-1)}(\lambda)
=(pm-1)![-mJ(\lambda)U(\lambda)v(\lambda)^p].
\tag{NB1.3}
$$

**Proof.** Subtract the correction recurrence at each step:
$f_{i+1}-C_{i+1}=M_i(f_i-C_i)$. Induction gives the product identity. Each individual native generator has the unit or completion factorization proved above. Substitute $Z=x^mv$ and the visible simple-pole expansion of $f_0$. The remaining analytic factor is nonzero at the center. Taylor expansion gives the order and factorial-normalized derivative. No value of totalized division at the center is used. $\square$

The invariant concerns the corrected expression. Without the correction, $f_0=1/x$, $M=x$, $B=-1$ yields raw output zero. The original OPICA affine-cancellation control remains necessary.

### 3.3 What makes this native, and what it does not cover

The theorem is not obtained by defining an admissible transformation to be one that preserves nonzero classes. It verifies a concrete family against the original $j$, the actual $N,M_\mu,\Pi$, finite Euler factors and the current completion. It is nevertheless a composition/instantiation result, not an independent exclusion of the hypothetical zero.

Arbitrary contact changes, nonlocal spectral maps, general projections, arbitrary nonlinear operations, and all historical CCM constructions are **not** classified by NB1. A local unit is not automatically a bounded isomorphism on the global functional domain. A new inequality on one of these very representations could still prove an exclusion; NB1 does not prohibit it.

### 3.4 Moving words: local cost is not global cost

At a fixed hypothetical $\lambda$, the logarithm of the normalized leading coefficient is explicitly priced by total delay, source order, Euler masses, rational factors and completion count. For $\sigma=\Re\rho>1/2$,

$$
|\log|E_Q(\lambda)||
\le\sum_{p\mid Q}-\log(1-p^{-\sigma})
\le C_\sigma\sum_{p\mid Q}p^{-\sigma}.
$$

A delay costs $\tau\delta$; source order $d$ costs $d\,|\log|\lambda^2-1/4||$. Residual powers cost zero in the *leading value* at $\lambda$, since their value is one. They can still have large derivatives and large norms elsewhere.

For an unnormalized derivative, the additional $(pm-1)!$ costs $O_m(p\log(p+2))$. These calculations are not a J5.2/MS1 proof. Passing to growing words or limits still requires global domain estimates and the topology appropriate to the observation. The fixed-source and moving-source window theorems retain their inherited paper status.

---

## R1 4. AT1 — A weaker, sufficient arithmetic rate-transfer law

### 4.1 Why the old requirement was stronger than needed

The DC/MS continuation establishes an exact field decomposition $F=S+B$, where $S$ is the Type I field and $B$ the balanced field. Its older absolute-energy comparison uses

$$
\left|\int_I|F|^2-\mathcal Q_B(c,c)\right|
\le K_\ell+4W eV e^{T/2}+We^2,
\tag{AT1.0}
$$

with $e=\|S\|_{\infty,I}$. This is useful when an **absolute subexponential energy error** is required. But retaining only the logarithmic energy rate does not require that stronger property. [S3]

### 4.2 The norm-first comparison

Let $F,S,B\in L^2(I)$, real or complex, satisfy $F=S+B$. Let $L,Q$ be real numbers satisfying

$$
Q=\|B\|_2^2-L.
$$

Then

$$
\boxed{
\left|\log(1+\|F\|_2^2)-\log(1+[Q]_+)\right|
\le2\log(1+\|S\|_2)+\log(1+|L|).
}
\tag{AT1.1}
$$

**Proof.** Work in the augmented Hilbert space with vectors $(1,F)$ and $(1,B)$. Reverse triangle gives

$$
\left|\sqrt{1+\|F\|_2^2}-\sqrt{1+\|B\|_2^2}\right|
\le\|S\|_2.
$$

Both square roots are at least one. Each is therefore at most the other multiplied by $1+\|S\|_2$. Taking logarithms proves

$$
|\log(1+\|F\|_2^2)-\log(1+\|B\|_2^2)|
\le2\log(1+\|S\|_2).
$$

The elementary positive-part logarithmic inequality applied to $\|B\|_2^2$ and $Q$ bounds the remaining difference by $\log(1+|L|)$. Add the two bounds. $\square$

Consequently, for any positive horizons $T_n\to\infty$, the conditions

$$
\log(1+\|S_n\|_2)=o(T_n),\qquad
\log(1+|L_n|)=o(T_n)
\tag{AT1.2}
$$

imply

$$
\frac{\log(1+\|F_n\|_2^2)}{2T_n}
-
\frac{\log(1+[Q_n]_+)}{2T_n}\longrightarrow0.
\tag{AT1.3}
$$

This transfers limits and extended limsup/liminf rates. It does not assert that their raw energy difference is subexponential.

For example, on a unit interval take constant fields $B_n=e^{\theta T_n}$, $S_n=1$, with $\theta>0$. Both full and balanced energies have rate $\theta$, but their difference is $2e^{\theta T_n}+1$, which has a positive logarithmic rate. Thus AT1 genuinely relaxes the transfer requirement.

### 4.3 Exact native mask instance

Freeze each finite squarefree palette $Q$ on its entire window $I=[H,T]$, $0\le H<T$, and put

$$
w_d(t)=d^{-1/2}U_{d_{\rm src},Q}(t-\log d),\qquad
X_x(t)=\sum_d x(d)w_d(t).
$$

Use a measurable cutoff and the low mask $\max(d,e)/\gcd(d,e)\le B(t)$, with $1\le B(t)\le B_*$. It includes the diagonal. Its strict complement defines the real high-primitive quadratic form. All sums are finite at a fixed horizon by causality.

For the literal binomial inverse coefficients, $v_Q=s_r+c_r$. Thus

$$
F=X_{v_Q},\quad S=X_{s_r},\quad B=X_{c_r},\qquad
\mathcal Q_B(c_r,c_r)=\|B\|_2^2-\mathcal L_B(c_r,c_r).
$$

With $\ell=2r-1$, the actual bound $|c_r(d)|\le d_\ell(d)$ and $V=\|U_{d_{\rm src},Q}\|_\infty$ give

$$
|\mathcal L_B(c_r,c_r)|\le
K_\ell=4WV^2B_*(1+\log B_*)^{2\ell-2}(1+T)^{\ell^2}.
\tag{AT1.4}
$$

For clarity, this estimate writes $d=ha,e=hb$, keeps the actual coefficients until absolute values are taken, and then bounds by

$$
V^2\left(\sum_{a\le B_*}\frac{d_\ell(a)}{\sqrt a}\right)^2
\sum_{h\le e^T}\frac{d_\ell(h)^2}{h}.
$$

The divisor bounds in DC1 give (AT1.4). No false assumption that the common gcd is coprime to both primitive indices is inserted. [S3]

AT1 now requires only

$$
\log(1+\|X_{s_r}\|_{L^2(I)})=o(T),\qquad
\log(1+K_\ell)=o(T).
\tag{AT1.5}
$$

It does not require an $e^{-T}$ Type I error or control the mixed energy by a crude $e^{T/2}$ upper. The low-mask estimate is still necessary: an unmasked scalar identity does not by itself identify a high-mask observation.

Identifying the full energy rate with $\Theta$ remains a separate source-correct theorem. For fixed source this is J5.2; for changing source orders it requires the MS1 argument and its uniform constants. Neither is silently formalized here. [S5, S6]

---

## R1 5. AT2 — Where a large native observation must go

In the same exact decomposition,

$$
\boxed{
\|F\|_2^2
\le2\|S\|_2^2+2[\mathcal Q_B(c,c)]_++2|\mathcal L_B(c,c)|.
}
\tag{AT2.1}
$$

**Proof.** Triangle and $(u+v)^2\le2u^2+2v^2$ give $\|F\|^2\le2\|S\|^2+2\|B\|^2$. Substitute $\|B\|^2=\mathcal Q_B(c,c)+\mathcal L_B(c,c)$, then use the positive part and absolute value. $\square$

If the low form is bounded by $K_n$ and

$$
M_n=\max\{\|S_n\|_2^2,[\mathcal Q_{B_n}(c_n,c_n)]_+\},
$$

then $\|F_n\|^2\le4M_n+2K_n$. If the native energy has a full positive rate $\Theta$ and $K_n$ has rate zero, then

$$
\boxed{\liminf_n\frac{\log(1+M_n)}{2T_n}\ge\Theta.}
\tag{AT2.2}
$$

For any $b<\Theta$, the complete energy eventually dominates an exponential with rate $b$, while $K_n$ is negligible at that scale; solve the preceding inequality for $M_n$, then let $b\uparrow\Theta$.

No equality is asserted. Very large Type I and balanced fields can cancel, making both norms grow faster than their sum. Nor must the same branch realize the maximum at every horizon.

AT2 gives a precise allocation statement for the old terminal-cutoff experiment: making the balanced field identically zero on a finite window forces the complete signal into the retained term. It also audits arbitrary proposed schedules without assuming that each stage is already “good.” It is still not an independent signed bound.

---

## R1 6. HT1 — Noncompact dilation mixing with a valid inverse

### 6.1 Relation to the historical result

M0043 already proves the compact signed mixing theorem. It explicitly cautions that noncompact mixing needs a new domain and inversion argument. The following is an extension to a concrete absolutely convergent noncompact class, not a rediscovery of the compact theorem and not a classification of every co-Poisson construction. [S4]

Use the heat-variable Fourier convention

$$
\widehat\phi(\xi)=\int\phi(x)e^{-2\pi ix\xi}\,dx,
\qquad
D_t=e^{t/2}\sum_{n\in\mathbb Z}\delta_{e^t n}.
$$

Poisson summation on Schwartz tests gives $\mathcal F D_t=D_{-t}$.

Let $\sigma$ be a signed or complex Borel measure with

$$
\int e^{a|t|}\,d|\sigma|(t)<\infty
\quad\text{for some }a>1/2.
\tag{HT1.1}
$$

Define the heat mixture $\nu_\sigma=\int D_t\,d\sigma(t)$.

### 6.2 Existence and Fourier transport

For $R\ge0$, counting lattice points gives

$$
|\nu_\sigma|([-R,R])
\le2R\int e^{-t/2}\,d|\sigma|(t)
+\int e^{t/2}\,d|\sigma|(t).
\tag{HT1.2}
$$

Both integrals are finite. This proves local finiteness and linear total-variation growth. The same counting estimate, or a dyadic decomposition, bounds pairings with a Schwartz test by a finite seminorm times $e^{t/2}+e^{-t/2}$. Absolute dominated integration therefore justifies

$$
\boxed{\widehat{\nu_\sigma}=\nu_{\sigma^\vee},\qquad
\sigma^\vee(A)=\sigma(-A).}
\tag{HT1.3}
$$

The origin atom is $\int e^{t/2}\,d\sigma(t)$. These are genuine measure/distribution identities, not formal evaluations of a continued transform.

### 6.3 Weighted arithmetic inverse

Restrict $\nu_\sigma$ to the positive heat axis, push forward by $x\mapsto y=\log x$, and multiply by $e^{-y/2}$. Call the result $\eta$. The weight of an atom $x=e^t n$, $n\ge1$, becomes $n^{-1/2}$, so

$$
\eta=N*\sigma.
\tag{HT1.4}
$$

For a measure $\tau$, define the weighted variation norm

$$
\|\tau\|_{-a}=\int e^{-ay}\,d|\tau|(y).
$$

It is submultiplicative for convolution whenever the two norms are finite, by absolute Fubini. Put $s=a+1/2>1$. Then

$$
\|N\|_{-a}=\zeta(s),\qquad
\|M_\mu\|_{-a}=\sum_{n\ge1}|\mu(n)|n^{-s}
=\frac{\zeta(s)}{\zeta(2s)}.
\tag{HT1.5}
$$

The last equality follows from the absolutely convergent squarefree Euler product. The norm of $\sigma$ is finite by (HT1.1). Thus all the required convolutions are absolutely defined in this weighted algebra. The actual finite-divisor identity gives

$$
\boxed{M_\mu*N=\delta_0,\qquad \sigma=M_\mu*\eta.}
\tag{HT1.6}
$$

In particular the mixture map is injective. This step is the new noncompact-domain obligation; compact support is not being tacitly used in the inverse.

### 6.4 Noncompact sharp-gap theorem

**Statement.** Under (HT1.1), if $\nu_\sigma$ is Fourier self-dual and

$$
\nu_\sigma|_{(-1,1)\setminus\{0\}}=0
\quad\text{as a restriction of measures},
$$

then $\sigma=c\delta_0$ and $\nu_\sigma=cD_0$. If the origin atom is also zero, $\nu_\sigma=0$.

**Proof.** By (HT1.3) and injectivity, self-duality implies $\sigma=\sigma^\vee$. The gap makes $\eta$ vanish on $(-\infty,0)$. The Möbius inverse is causal, so (HT1.6) implies that $\sigma$ also vanishes there. Evenness then concentrates $\sigma$ at zero. A measure concentrated at zero is a scalar delta. Substitution proves the result. $\square$

No positivity premise is needed. The conclusion is confined to the exponentially integrable mixing class. Critical or slowly decaying, conditionally defined, or renormalized distributions are not covered.

### 6.5 Quantitative gap leakage

Causality of $M_\mu$ implies that the negative-axis part of $\sigma$ depends only on the negative-axis part of $\eta$. Taking weighted variation in (HT1.6),

$$
\|\sigma|_{(-\infty,0)}\|_{-a}
\le\frac{\zeta(s)}{\zeta(2s)}
\|\eta|_{(-\infty,0)}\|_{-a}.
$$

The log pushforward is injective and has a positive weight, so total variations transform exactly. Consequently

$$
\boxed{
\int_{(0,1)}x^{-a-1/2}\,d|\nu_\sigma|(x)
\ge
\frac{\zeta(2a+1)}{\zeta(a+1/2)}
\int_{(-\infty,0)}e^{-at}\,d|\sigma|(t).
}
\tag{HT1.7}
$$

The bound measures variation, not signed net mass; cancellation inside the gap cannot evade it. It gives a positive leakage lower bound for every even mixer with nonzero mass off the origin.

### 6.6 A pointwise density version

Suppose instead that $h$ is continuous, even, and $|h(t)|\le He^{-b|t|}$, $b>1/2$. Its mixture has positive-axis density

$$
r_h(x)=\frac1{\sqrt x}\sum_{n\ge1}\frac{h(\log(x/n))}{\sqrt n},
\qquad x>0.
\tag{HT1.8}
$$

The series converges locally uniformly. With $g(y)=e^{y/2}r_h(e^y)$, we have $g=N*h$. For $y\le0$,

$$
\sum_{m,n\ge1}\frac{|h(y-\log(mn))|}{\sqrt{mn}}
\le He^{by}\zeta(b+1/2)^2.
$$

This justifies the double-series inverse directly in the negative-half-line weighted supremum norm. It yields

$$
\boxed{
\sup_{0<x<1}x^{1/2-b}|r_h(x)|
\ge\frac{\zeta(2b+1)}{\zeta(b+1/2)}
\sup_{t\ge0}e^{bt}|h(t)|.
}
\tag{HT1.9}
$$

This supremum proof is separate from the measure norm at exponent $b$; it does not assume that $\int e^{b|t|}|h(t)|dt$ is finite at the endpoint. The measure theorem applies at any $a\in(1/2,b)$.

Also $r_h(x)=O(x^{b-1/2})\to0$ as $x\downarrow0$. Hence adding a constant density $c\,dx$ and an arbitrary lattice-supported measure cannot repair the gap: on $(0,1)$ the density would be $r_h+c$, forcing $c=0$, then $h=0$ by (HT1.9). If the remaining lattice measure is self-dual and has zero origin atom, it is zero. This explicitly covers the usual affine origin correction $\delta_0+dx$, rather than silently discarding it. Arbitrary nonconstant or nonlattice corrections remain outside this corollary.

---

## R1 7. A completed noncompact closing attempt, and its failure

Consider the explicit even density

$$
h(t)=e^{-|t|}-\frac52e^{-2|t|}.
$$

It is noncompact, exponentially integrable in the required range, and

$$
\int e^{t/2}h(t)dt=\frac83-\frac52\frac{16}{15}=0.
$$

Thus its heat mixture is a well-defined self-dual signed measure of linear variation growth with **zero origin atom**. Convergence and normalization have genuinely been repaired.

For $0<x<1$, every logarithmic argument in (HT1.8) is negative, giving

$$
r_h(x)=\sqrt x\,\zeta(3/2)-\frac52x^{3/2}\zeta(5/2).
$$

At $x=1/8$, the elementary bounds $\zeta(3/2)\ge1$ and $\zeta(5/2)\le1+\int_1^\infty t^{-5/2}dt=5/3$ show

$$
\boxed{r_h(1/8)\ge\frac{23}{48\sqrt8}>0.}
\tag{HT1.10}
$$

The exact unit gap fails. This is an auxiliary heat construction, not a claimed contact-to-heat map from an actual zero. It falsifies the idea that merely replacing compact mixing by convergent noncompact mixing solves the historical support problem.

The same obstruction applies to the literal compact source $j$, viewed as a mixing density. In its first lattice band, before any contribution from $n=2$,

$$
r_j(x)=x^{-1/2}j(\log x),\qquad e^{-s_0}<x<e^{s_0}.
$$

The source is nonzero (indeed integration by parts gives $\int j=1/16$), even and compact, with $\int e^{t/2}j(t)dt=0$. Thus it has both positive and negative values. The first band exhibits both signs off the integer lattice, and HT1 gives unavoidable interior-gap leakage. Its exact Fourier transport is not a positive sharp-gap defect. This application uses the actual source and explains which requirements fail; it is not a restriction on the location of its zeta zeros.

---

## R1 8. HT2 — Nearly sharp gaps do not automatically survive a limit

Let $\nu$ be an even real locally finite signed measure with

$$
\widehat\nu=\nu,\qquad |\nu|([-R,R])\le C(1+R),\qquad
\nu|_{\mathbb R\setminus\mathbb Z}\ge0.
$$

Suppose $\nu|_{(-a,a)}=0$, where $0<a\le1$. The origin atom is then zero. Set

$$
s(x)=\left(\frac{\sin\pi x}{\pi x}\right)^2,
\qquad \Delta(x)=(1-|x|)_+.
$$

The Gaussian-regularized pairing proof in OPICA H1 establishes $\int s\,d\nu=\int\Delta\,d\nu$ for this growth class. Briefly, multiply $s$ by a Gaussian, use $\widehat s=\Delta$, dominate the left side by $(1+x^2)^{-1}$, and the regularized right side by a bounded compact part plus a uniform Gaussian tail. Linear variation growth makes both majorants integrable. [S2, H1]

Because $s$ vanishes at the nonzero integers and $\Delta\le1-a$ outside the gap,

$$
0\le\int_{\mathbb R\setminus\mathbb Z}s\,d\nu
\le(1-a)|\nu|([-1,1])\le2C(1-a).
\tag{HT2.1}
$$

For $R\ge1$, $0<d\le1/2$, define

$$
E_{R,d}=\{x:|x|\le R,\ \operatorname{dist}(x,\mathbb Z)\ge d\}.
$$

On this set, $s(x)\ge4d^2/(\pi^2R^2)$. Hence

$$
\boxed{
\nu(E_{R,d})
\le\frac{\pi^2R^2}{4d^2}(1-a)|\nu|([-1,1])
\le\frac{\pi^2R^2C}{2d^2}(1-a).
}
\tag{HT2.2}
$$

A family with a fixed positive mass away from the integers and gap $a\uparrow1$ therefore must pay an unbounded local variation cost. This is a quantitative restriction, not a new assumption that every approximation has bounded cost.

### 8.1 The controlled limiting theorem

Suppose $\nu_n$ satisfy these hypotheses with one common $C$, and $a_n\to1$ from below. Then

$$
\boxed{\nu_n\longrightarrow0\quad\text{on every Schwartz test}.}
\tag{HT2.3}
$$

**Proof.** Uniform local variation bounds give subsequential weak-* compactness on each compact interval; a diagonal subsequence yields a locally finite signed-measure limit. The common linear growth controls Schwartz tails uniformly, so the subsequence converges on Schwartz tests. Fourier transformation preserves that test class, hence self-duality passes to the limit. Every compact subset of $(-1,1)$ is eventually in the gap. Positivity off the lattice passes by testing nonnegative compact functions supported in $\mathbb R\setminus\mathbb Z$. The limit satisfies the exact H1 hypotheses, so it is zero. Every subsequence has only that possible limit, proving (HT2.3). $\square$

No convergence in total variation is claimed. Nonzero mass may approach the lattice and cancel weakly with signed lattice mass. The conclusion explains why a controlled near-gap induction does not by itself produce a nonzero critical-gap measure.

---

## R1 9. CT1 — An explicit almost-gapped family and its inadmissible normalized limit

Take $0<L<\log2$, $r=e^L$, and define

$$
\boxed{\nu_L=D_L+D_{-L}-2\cosh(L/2)D_0.}
\tag{CT1.1}
$$

This family has the following exact properties:

- It is even and Fourier self-dual, since Fourier swaps $D_L,D_{-L}$ and fixes $D_0$.
- The origin atom is zero: $e^{L/2}+e^{-L/2}-2\cosh(L/2)=0$.
- It is nonnegative off $\mathbb Z$; its only negative summand is supported on $\mathbb Z$.
- It has gap $(-e^{-L},e^{-L})$, and is nonzero because of its atom at $e^{-L}$.
- Its total variation has one uniform linear-growth bound for $0<L<\log2$.

Thus nonzero subcritical-gap measures really exist. HT2 predicts, correctly, that their unnormalized limit is zero.

Trying to retain a nonzero observation by division by $L^2$ gives a different domain. On Schwartz tests, the map $t\mapsto D_t$ is twice differentiable near zero, with differentiation justified by uniform rapidly decaying lattice sums. Taylor expansion gives

$$
\boxed{
\frac{\nu_L}{L^2}\longrightarrow D''_0-\tfrac14D_0
=\sum_{n\in\mathbb Z}\bigl(n^2\delta_n''-2n\delta_n'\bigr).
}
\tag{CT1.2}
$$

Indeed the pairing of the right side with $\phi$ is
$\sum_n[n^2\phi''(n)+2n\phi'(n)]$. The $\delta_0$ coefficient cancels. A nonzero second derivative of a delta remains at $n=1$; the limit is not an order-zero signed measure.

Also

$$
|\nu_L/L^2|([-2,2])\ge2e^{-L/2}/L^2\longrightarrow\infty.
$$

So the hypothesis needed for the measure limit was actually lost. This is an explicit failure of the normalized approximation mechanism, not a counterexample to H1.

The nonsmooth-frequency/sinc pairing gives an additional exact check. For $1<r<2$, only the two atoms at $\pm1/r$ contribute to the triangle pairing after origin cancellation, and therefore

$$
\int s\,d\nu_L=\int\Delta\,d\nu_L
=\frac{2(r-1)}{r^{3/2}}.
\tag{CT1.3}
$$

This behaves linearly in $L$, whereas the Schwartz-test expansion in (CT1.2) begins at order $L^2$. There is no contradiction: $s$ is not a Schwartz test, and the normalized variation has no uniform tail bound. Interchanging this limit with that pairing would be another invalid domain step.

---

## R1 10. MC1 — A multi-zero conditioning test that must be passed

The archive already contains finite confluent Gram bounds, optimal Laguerre leakage and a Hardy/Blaschke range description. This section does not claim them as new. It tests the stronger hope that a nearly singular multi-zero Gram automatically amplifies the actual coupled input into a contradiction. [S7]

For $0<h<1$, take the auxiliary rational inner function

$$
A_h(z)=\frac{(z-1)^2-h^2}{(z+1)^2-h^2},\qquad Y_h=-A'_h.
$$

Its zeros are $\lambda_1=1-h$, $\lambda_2=1+h$. The true $L^2(0,\infty)$ Gram matrix of the corresponding exponential evaluation functions is

$$
G_h=\begin{pmatrix}
[2(1-h)]^{-1}&1/2\\
1/2&[2(1+h)]^{-1}
\end{pmatrix},\quad
\det G_h=\frac{h^2}{4(1-h^2)}.
$$

The source-coupled target vector is

$$
b_h=\left(\frac{h}{2(1-h)},-\frac{h}{2(1+h)}\right)^T.
$$

Direct algebra gives

$$
\boxed{b_h^*G_h^{-1}b_h=\frac{2-h^2}{1-h^2}\longrightarrow2
\quad(h\downarrow0).}
\tag{MC1.1}
$$

The inverse matrix becomes ill-conditioned, but the coupled data vanish in the corresponding direction. A determinant estimate alone does not force the observed quantity to blow up.

This is an auxiliary analytic control, not an actual off-line zeta configuration and not a model preserving every native arithmetic or positivity condition. It rejects only the automatic conditioning inference. It leaves open source-sensitive multi-zero estimates, provided their right-hand sides and conditioning costs are treated jointly.

---

## R1 10.5 CP1 — A renormalized, actual-zero-generated measure: the sign fails explicitly

HT1 does not exclude a properly renormalized co-Poisson construction. I therefore tested that possibility rather than stopping at the mixing obstruction. The calculation below supplies a genuine measure from a zeta zero and proves exactly which closing hypothesis fails. The construction uses the genuine theta/integer comb, not the fixed source $j$; it is an explicitly different map, not an asserted identification with the contact observation. Related co-Poisson constructions are classical; general novelty is not claimed. [W1, W2]

### The convergent distributional construction

For $t\ge0$, set

$$
A_t=D_t-e^{t/2}\delta_0,\qquad
K_t=A_t+\mathcal F A_t
=D_t+D_{-t}-e^{t/2}(\delta_0+dx).
\tag{CP1.1}
$$

Every $K_t$ is even and self-dual. For a Schwartz test $\phi$ and every integer $N>1$,

$$
|\langle A_t,\phi\rangle|
=\left|e^{t/2}\sum_{n\ne0}\phi(e^tn)\right|
\le2\zeta(N)\,p_N(\phi)e^{-(N-1/2)t},
$$

where $p_N(\phi)=\sup_x(1+|x|)^N|\phi(x)|$. The same estimate applies to $\mathcal F A_t$ using a Schwartz seminorm of $\widehat\phi$. Thus

$$
V_\lambda=\int_0^\infty e^{-\lambda t}K_t\,dt
\tag{CP1.2}
$$

is an entire tempered-distribution-valued family in $\lambda$, defined by absolutely convergent **Schwartz-test** integrals. No claim is made that the integral of the total variations of its summands converges. The subtraction is performed before taking the limit, and self-duality follows on that test class.

### Prove that the relevant continuation is an order-zero measure

Put $\rho=1/2+\lambda$, $0<\sigma=\Re\rho<1$. This is precisely the interior critical-strip domain. On $x>0$, define

$$
S_\rho(x)=x^{-\rho}\sum_{n\le x}n^{\rho-1}
-x^{\rho-1}\sum_{n\le x}n^{-\rho}.
\tag{CP1.3}
$$

Real positive powers use the real logarithm. At an integer, the two newly entering summands cancel, so this formula has a continuous extension across the entry point.

The distribution $V_\lambda$ is the locally finite complex measure with origin atom $1/\rho$ and even density, away from the origin,

$$
\boxed{
R_\rho(x)=S_\rho(|x|)
+\zeta(\rho)|x|^{\rho-1}+\frac1{1-\rho}.
}
\tag{CP1.4}
$$

Here is a direct convergence justification, essential for the claim that this is a measure. Cut (CP1.2) off at $t=T$. For noninteger $x>0$ and $T$ large enough on a fixed compact interval, its positive-axis density is

$$
x^{-\rho}\sum_{n\le x}n^{\rho-1}
+x^{\rho-1}\sum_{x<n\le xe^T}n^{-\rho}
-\frac{e^{(1-\rho)T}-1}{1-\rho}.
\tag{CP1.5}
$$

For $X\ge1$, the elementary sum-integral comparison gives

$$
\sum_{n\le X}n^{-\rho}
=\frac{X^{1-\rho}}{1-\rho}+\zeta(\rho)+O_\rho(X^{-\sigma}).
\tag{CP1.6}
$$

To justify the constant without using a divergent Dirichlet series, subtract the displayed integral term, compare adjacent unit intervals by the derivative of $u^{-\rho}$, and sum the absolutely integrable derivative tail. The limit is locally holomorphic for $\Re\rho>0$, $\rho\ne1$, and agrees with $\zeta(\rho)$ on $\Re\rho>1$; analytic continuation identifies it. Equation (CP1.6), not an unregularized infinite sum, is what is used in (CP1.5).

On $e^{-T}\le x\le R$, the density error is $O_\rho(x^{-1}e^{-\sigma T})$. Its integral is $O_{\rho,R}((1+T)e^{-\sigma T})$. On $0<x<e^{-T}$, the truncated lattice sums vanish, and the remaining constant together with the integrable limiting $x^{\rho-1}$ term gives the same vanishing error. The origin atom of the truncated construction is $(1-e^{-\rho T})/\rho$. Thus the cutoff measures converge **locally in total variation** to (CP1.4) with that origin atom. This identifies the independently defined distributional limit with an order-zero measure; no extra delta atom is hidden at zero.

For $x\ge1$, elementary absolute bounds on the two finite sums show $S_\rho(x)=O_\rho(1)$. Near zero, $S_\rho=0$ and $|x|^{\rho-1}$ is locally integrable because $\sigma>0$. Therefore this measure has linear total-variation growth.

### The zero-generated, origin-corrected object

Now suppose $\zeta(\rho)=0$, with $0<\Re\rho<1$, $\rho\ne1/2$. Let

$$
c_\rho=\frac1{1-\rho},\qquad
b_\rho=\frac1\rho-\frac1{1-\rho}
=\frac{1-2\rho}{\rho(1-\rho)}\ne0.
$$

Define

$$
\mu_\rho=V_{\rho-1/2}
-c_\rho(\delta_0+dx)-b_\rho D_0.
\tag{CP1.7}
$$

Both correction measures are self-dual. The origin mass is $1/\rho-c_\rho-b_\rho=0$. Equation (CP1.4) shows

$$
\mu_\rho=S_\rho(|x|)\,dx
-b_\rho\sum_{n\in\mathbb Z\setminus\{0\}}\delta_n.
$$

Taking the real part after division by $b_\rho$ gives

$$
\boxed{
\eta_\rho=f_\rho(x)\,dx
-\sum_{n\in\mathbb Z\setminus\{0\}}\delta_n,
\qquad
f_\rho(x)=\Re\frac{S_\rho(|x|)}{b_\rho}.
}
\tag{CP1.8}
$$

This real-part step preserves Fourier self-duality because the input distribution is even; conjugation then commutes with its Fourier transform. The resulting $\eta_\rho$ is a **nonzero, real, even, self-dual, locally finite signed measure of linear variation growth, with exact open unit gap and zero origin atom**. It is nonzero because its atom at 1 is $-1$, which an absolutely continuous density cannot cancel. No simplicity assumption is needed: the construction uses only the zero equation, so it applies to any multiplicity.

This genuinely supplies every hypothesis of the proposed H1 contradiction **except off-lattice nonnegativity**. It does not prove that missing hypothesis.

### An explicit negative value on the first interval

Write $\lambda=\delta+i\gamma$. For $1<x<2$, set $u=\log x$. Only $n=1$ enters the finite sums, so

$$
\frac{S_\rho(x)}{b_\rho}
=e^{-u/2}\frac{1/4-\lambda^2}{\lambda}\sinh(\lambda u).
\tag{CP1.9}
$$

Assume $|\gamma|>3\pi/(2\log2)$, and choose
$u=3\pi/(2|\gamma|)$, hence $1<e^u<2$. The cosine is zero, and the sine has the sign that gives

$$
\boxed{
f_\rho(e^u)
=-|\gamma|\left(1+\frac1{4(\delta^2+\gamma^2)}\right)
 e^{-u/2}\cosh(\delta u)<0.
}
\tag{CP1.10}
$$

This follows by writing $(1/4-\lambda^2)/\lambda=1/(4\lambda)-\lambda$: its imaginary part is $-\gamma[1+1/(4(\delta^2+\gamma^2))]$. Continuity makes the negative value a negative-density interval, not an irrelevant pointwise representative.

No numerical assertion about the minimum height of actual zeta zeros is required for the theorem; the height condition is explicit. More generally H1 itself forces failure of off-lattice positivity for every zero for which (CP1.8) is constructed. The explicit formula locates that failure in the stated height range.

The same negative value occurs at $\delta=0$. Consequently this particular positivity target does not distinguish critical-line zeros from hypothetical off-line zeros. Asking it to be nonnegative would contradict an explicit formula, not supply a promising unproved estimate. This **closes this candidate proof attempt negatively** while preserving a legitimate, source-derived mathematical construction.

### Scalar phase tuning cannot repair the first interval either

For an off-line zero with $\delta\ne0$ and $|\gamma|>2\pi/\log2$, every nonzero real projection $\Re(\alpha\mu_\rho)$, $\alpha\in\mathbb C\setminus\{0\}$, has both signs in its off-lattice density on $(1,2)$.

To see this, take $\gamma>0$ by conjugation and use $S_\rho(e^u)=-2e^{-u/2}\sinh((\delta+i\gamma)u)$. If $\Im\alpha\ne0$, evaluation at $u=\pi/(2\gamma)$ and $u=3\pi/(2\gamma)$ gives opposite nonzero signs proportional to $\Im\alpha$. If $\alpha$ is real and nonzero, evaluation at $u=\pi/\gamma$ and $u=2\pi/\gamma$ gives opposite nonzero signs proportional to $\alpha\sinh(\delta u)$. All four points lie in the first lattice interval under the stated height bound. Lattice-supported corrections do not alter that density.

When $\delta=0$, a real scalar projection of the purely imaginary $\mu_\rho$ is zero; the nonzero projections still have the alternating sine signs. Thus simply changing the scalar phase either preserves a sign failure or destroys the observation. This is a single-zero-family statement, not a classification of arbitrary multi-zero or nonlocal maps.

### What this calculation changes

The raw noncompact comb proposal was not admissible. Renormalization really can repair its convergence and produce an order-zero measure; it is incorrect to conclude that all such repairs inevitably remain distributions. But for the explicit native-zero construction above, the gap/origin/duality obligations merely expose the remaining sign failure, which can be falsified inside one finite lattice interval. Further heat research needs a different source-sensitive sign mechanism, not a repetition of this normalization.

## R1 15. Source register

### User and project sources

**S1.** User-supplied `Pasted text(20261021-001152).txt`, “What remains after the OPICA PR?”, 245 rendered lines. Basis for the requested division of work; treated as a proposal, not theorem authority.

**S2.** `OPICA_Paper_Construction_v1_0_2026-10-21.md`; Drive ID `1Yyxs-ZsxwMpoJUit7qJWjTlzdLt7mZR9`. Fresh complete raw read and SHA-256 match. Sections 4–10 supply the existing generic architecture and sharp-gap pairing. The PR build specification is preserved as a separate scoped input.

**S3.** “Divisor-controlled mask transfer and moving-source continuation,” 20 October 2026; Drive document `1KcUovuIEsqhmJ25Yqn3U-ItDmLVEVRJx-_Ltpp_CYTA`. Preserved 27,129-byte text export, especially DC1/DC2 and MS1. Inherited PAPER/self-review, not a new live edit or independent proof check.

**S4.** M0043, `01_SHARP_GAP_DILATION_TRANSPORT.md`, original pages 6278–6282 of `RH_Step4_Third_Party_Complete_Handover.pdf`. The archive reports original-source SHA-256 `1859c1364f908fb9f59cd374f4a0bc9fd7a065c39846f288438a9a6f21e3aaab`. The included local extraction has its own hash and is **not** represented as those original raw bytes. Full source block read; page 6279 rendered and inspected.

**S5.** M0659, `continuation_native_j.md`, original balanced arithmetic / J4 / J5.2 source. The preserved raw body was recovered from the earlier OPICA evidence package. Inherited PAPER authority.

**S6.** M1196, `round4_energy.md`, logarithmic-window/auxiliary-completion source. Preserved raw body; inherited PAPER authority. No new formalization of its uniform estimates.

**S7.** Historical A03 dual-leakage and B04 range records in the full handover: finite confluent Gram infrastructure, optimal Laguerre leakage, rational inner-model controls, and closed-range zero-jet characterization. Retrieved excerpts were used to prevent rediscovery and overclaiming; no full independent re-proof of all those records is claimed.

### Repository sources

**R1.** Fresh main ref and open-PR collection reads for `HMarcusWH/zeta-23-lean`; exact responses summarized in `receipts/live_read_scope.json`.

**R2.** `Zeta23/ExceptionalZero/NativeActualInputZeroJets.lean` at main pin; blob `82ccdf1a050d82c6a262e0264b61db66b56c37df`. Actual transform, multiplicity-sensitive nonzero jet, nonrange and residual-pairing invariance.

**R3.** `Zeta23/ExceptionalZero/NativeOriginalSourceLaplaceVisibility.lean` at main pin; blob `77046a1361b7a3ed4565b241b0882c8885f36676`. Literal original one-Q source identity and off-line nonvanishing.

**R4.** `Zeta23/ExceptionalZero/Step4OutputSufficiency.lean` at main pin; blob `88df03fc6a3ee762ec396f932c27f62c2217bc60`. Conditional A-X/B-Y/C-Schur implications; no supplied closing antecedent.

**R5.** `Zeta23/CCM/NativeIntegerPrimeConvolution.lean`, preserved pinned snapshot. Actual arithmetic identities; not independently recompiled in this round.

### External primary literature — context, not substituted proof

**W1.** Jean-François Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta function*, Journal de théorie des nombres de Bordeaux 16 (2004), 65–94, DOI 10.5802/jtnb.434. Primary publication page: https://numdam.org/item/JTNB_2004__16_1_65_0/ . Publication description checked; no claim to a full novelty review.

**W2.** Jean-François Burnol, *Entrelacement de co-Poisson*, Annales de l'Institut Fourier 57 (2007), 525–602, DOI 10.5802/aif.2268. Primary publication page: https://aif.centre-mersenne.org/articles/10.5802/aif.2268/ . Related harmonic/Hilbert/distributional framework; not used as an unexamined native closing theorem.

The full proofs of the new extensions are written in this report. Source citations, hashes and finite receipts are evidence of provenance and execution, not substitutes for those proofs.

# V. Round 2 complete technical proofs

These are the complete fifteen Round 2 statement families and proofs. Part II expands the separately named rate dependency. Part III adds the native sampling completion; it does not retrospectively change the historical claim that R2-S2 alone did not supply a sample estimate. Source-local citation keys are resolved at this part's end.

## R2 1. Fixed source, notation and the inherited inputs

Retain exactly

$$
s_0=1/4096,\qquad c_n=s_0/[n(n+1)],\qquad
q=*_{n\ge1}\frac{\mathbf1_{[-c_n,c_n]}}{2c_n},\qquad
P=\partial_t^2-\tfrac14,
$$

$$
j_m=P^{m+2}q,\qquad j_0=j,\qquad
J_m(z)=(z^2-\tfrac14)^{m+2}Q_0(z),\qquad
Q_0(z)=\prod_{n\ge1}\frac{\sinh(c_nz)}{c_nz}.
$$

There is one copy of $Q_0$, not the two-copy autocorrelation source. Put

$$
N=\sum_{n\ge1}n^{-1/2}\delta_{\log n},\quad
M=\sum_{n\ge1}\mu(n)n^{-1/2}\delta_{\log n},\quad
\Pi=\sum_{n\ge2}\Lambda(n)n^{-1/2}\delta_{\log n},
$$

$$
F_m=\Pi*j_m,\qquad U_m=(tN)*j_m,\qquad
R_{m,\ell}=N^{*\ell}*U_m,\qquad g=\log2-s_0>0.
$$

All these fields are actual smooth, locally finite histories. They vanish below $g$. For $0\le\ell\le m$,

$$
\widehat R_{m,\ell}(z)=-J_m(z)\zeta(z+\tfrac12)^\ell\zeta'(z+\tfrac12)
\tag{1.1}
$$

is entire. The only possible pole, at $z=1/2$, has order $\ell+2\le m+2$ and is removed by the actual source. No reciprocal zeta factor occurs in (1.1).

We use the source-identified J5.2 statement at inherited PAPER authority:

$$
\lim_{T\to\infty}\frac{\log(1+\int_{T-C\log T}^{T}|F_m(t)|^2dt)}{2T}=\Theta,
\quad C>1,\quad m\text{ fixed},
\tag{1.2}
$$

where $\Theta=\sup_{\rho}(\Re\rho-1/2)_+$. No zero attaining this supremum is assumed. The present fixed-order result does not invoke MS1. The full analytic proof of (1.2) is preserved as a dependency; the new forward-kernel estimate is not itself a proof of (1.2).

In the heat variable, Fourier transformation is

$$\widehat f(\xi)=\int_{\mathbb R}f(x)e^{-2\pi ix\xi}dx.$$

This convention is distinct from the logarithmic-source Laplace convention. Write $D_0=\sum_{n\in\mathbb Z}\delta_n$. A locally finite measure means an order-zero object; a formal derivative of a delta is not admitted as such.

## R2 2. Q1--Q2: quantitative fixed-order forward localization

### 2.1 Lemma Q1a: a vertical estimate uniform in the real part

There exist absolute source constants $A_q,c_q>0$ such that, for every real $\sigma,\tau$,

$$
\boxed{|Q_0(\sigma+i\tau)|\le A_q e^{s_0|\sigma|}e^{-c_q\sqrt{|\tau|}}.}
\tag{Q1.1}
$$

One possible choice in the argument is $A_q=8$ and $c_q=(\log8)\sqrt{s_0}/4$; a larger $A_q$ is harmless.

**Proof.** For any complex $w$, the integral representation of $\sinh w/w$ gives a bound $e^{|\Re w|}$. Also $|\sinh w|\le e^{|\Re w|}$ gives $e^{|\Re w|}/|w|$. Thus each factor is bounded by

$$e^{c_n|\sigma|}\min\{1,(c_n|\tau|)^{-1}\}.$$

Put $L=\sqrt{s_0|\tau|}/4$. When $L\ge1$, every $1\le n\le\lfloor L\rfloor$ has $c_n|\tau|\ge8$. Their product contributes at most $8^{-\lfloor L\rfloor}\le8e^{-(\log8)L}$. All other factors contribute at most their real exponential. Since $\sum c_n=s_0$, the claimed bound follows. When $L<1$, its right side with the displayed constant dominates $e^{s_0|\sigma|}$. Passage to the normally convergent product preserves the estimate. $\square$

This step is stronger than merely knowing a different vertical-strip constant for every strip.

### 2.2 Lemma Q1b: moving left-line zeta cost

There is a universal $A_0\ge1$ such that for every integer $n\ge1$ and real $\tau$,

$$
|\zeta(-n+i\tau)|+|\zeta'(-n+i\tau)|
\le A_0^{n+1}(n+2+|\tau|)^{n+2}.
\tag{Q1.2}
$$

**Proof.** On the disk of radius $1/4$ about $s=-n+i\tau$, use

$$\zeta(s)=2(2\pi)^{s-1}\sin(\pi s/2)\Gamma(1-s)\zeta(1-s).$$

The reflected zeta factor is bounded by $\zeta(7/4)$, because $\Re(1-s)\ge n+3/4\ge7/4$. Write $s=-n+w+i\tau$. Gamma recurrence gives

$$\Gamma(1-s)=\Gamma(1-w-i\tau)\prod_{j=1}^n(j-w-i\tau).$$

On $3/4\le\Re(1-w)\le5/4$, the standard uniform gamma estimate is a fixed polynomial in $1+|\tau|$ times $e^{-\pi|\tau|/2}$. The sine factor has at most the opposite exponential, including only a fixed disk-radius cost. The finite gamma product is at most $(n+2+|\tau|)^n$. Absorb the bounded remaining factors into the displayed envelope. Cauchy's derivative inequality on the disk gives the same type of bound for $\zeta'$ at its center. This proof uses no zero-free assertion. $\square$

The constants can be made numerical by selecting explicit gamma bounds. No numerical values of $A_0$ or the final localization constants are certified in this paper.

### 2.3 Theorem Q2: double-exponential forward decay

Fix integers $m\ge\ell\ge0$ and $d\ge0$. There are $A,c>0$, depending on these fixed orders and on the literal source only, such that

$$
\boxed{
|R_{m,\ell}^{(d)}(t)|
\le A\exp\{-c\exp(t/[2(\ell+1)])\},\qquad t\ge0.
}
\tag{Q2.1}
$$

**Proof.** Let $a=\ell+1$. The actual transform identity and elementary pole cancellation permit inverse Laplace integration on every line $z=-n-1/2+i\tau$, $n\ge1$. For each fixed $n$, the horizontal sides vanish by the source's vertical decay; no reciprocal-zeta bound is needed. On that line, Q1 gives

$$
|z^dJ_m(z)\zeta(z+1/2)^\ell\zeta'(z+1/2)|
\le C_0D_0^n (n+2+|\tau|)^{an+b}e^{-c_q\sqrt{|\tau|}},
\tag{Q2.2}
$$

with fixed $b=2a+2m+4+d$, after enlargement of constants. The factor $e^{s_0(n+1/2)}$ is included in $D_0^n$.

For $p=an+b$, split $(n+2+u)^p\le2^p[(n+2)^p+u^p]$ and use

$$\int_0^\infty u^p e^{-c_q\sqrt u}du=2\Gamma(2p+2)c_q^{-2p-2}.$$

A factorial bound gives fixed $C,D,B$ with

$$
\int_{\mathbb R}|z^dJ_m(z)\zeta(z+1/2)^\ell\zeta'(z+1/2)|d\tau
\le C e^{Dn}n^{2an+B}.
$$

Consequently, simultaneously for every integer $n\ge1$,

$$|R_{m,\ell}^{(d)}(t)|\le C e^{-(n+1/2)t}e^{Dn}n^{2an+B}.\tag{Q2.3}$$

Choose $\eta=e^{-(D+4)/(2a)}$ and, for sufficiently large $t$, $n=\lfloor\eta e^{t/(2a)}\rfloor$. Then

$$-nt+2an\log n+Dn\le-4n.$$

The factor $n^B$ is absorbed into half the negative exponential, and $n\ge\eta e^{t/(2a)}/2$. This proves (Q2.1) on the late tail. A larger $A$ covers the remaining compact interval, where the field is smooth. $\square$

**Quantifier audit.** The constants are uniform in the contour index $n$, which is explicitly priced before optimization. The source order $m$, convolution order $\ell$ and derivative order $d$ remain fixed. No claim about arbitrary growing orders is obtained from Q2.

For $\ell=0$, this agrees in scale with the historical first-drive Poisson estimate. The higher-$\ell$ exponent $1/[2(\ell+1)]$ is sufficient here; no optimality claim is made.

## R2 3. Q3: the exact native corridor needs only logarithmic slack

Fix $r\ge2$, $m\ge r-1$, $C>1$ and $\eta\ge0$. Allow a finite squarefree palette $Q_T$ satisfying

$$\log Q_T\le\eta\log T$$

for all sufficiently large $T$, and freeze it on the whole observation window. The trivial palette $Q_T=1$ is an important admissible choice. Put

$$
D_{Q_T}=\sum_{d\mid Q_T}\mu(d)d^{-1/2}\delta_{\log d},\qquad
M_{Q_T}=\sum_{(n,Q_T)=1}\mu(n)n^{-1/2}\delta_{\log n},
$$

$$U_{m,Q_T}=D_{Q_T}*U_m,\qquad
R_{m,\ell,Q_T}=D_{Q_T}^{*(\ell+1)}*R_{m,\ell}.$$

The local inverse and the literal field identity are unchanged. The filter mass obeys

$$b_{Q_T}=\prod_{p\mid Q_T}(1+p^{-1/2})\le Q_T\le T^\eta.$$

Choose a fixed

$$K>C+r\eta+2r$$

and set

$$
I_T=[T-C\log T,T],\quad
Y_T=e^{T/r}T^{-K/r},\quad
Z_T=e^{T/r-g}T^{K(r-1)/r}.
\tag{Q3.1}
$$

### 3.1 Theorem Q3

For all sufficiently large $T$, on the whole window $I_T$ there is an exact identity

$$F_m=E_T+\mathcal B_T,\tag{Q3.2}$$

where

$$
\mathcal B_T(t)=
\sum_{\substack{Y_T<n_1,\ldots,n_r\le Z_T\$n_1\cdots n_r,Q_T)=1}}
\frac{\mu(n_1)\cdots\mu(n_r)}{\sqrt{n_1\cdots n_r}}
R_{m,r-1,Q_T}(t-\log(n_1\cdots n_r))
\tag{Q3.3}
$$

and, for some fixed $c,C_1>0$,

$$
\boxed{
\|E_T\|_{\infty,I_T}
\le C_1T^{r\eta}\exp\{T/2-cT^p\},\qquad
p=\frac{K-C-r\eta}{2r}>1.
}
\tag{Q3.4}
$$

In particular the Type I error decreases faster than every fixed exponential in $T$. Every retained product is at most $e^{t-g}$. Repeated primes across factors remain included.

**Proof.** The exact binomial inverse identity is the same finite convolution identity as J17. If $m_{\le Y}$ is the small part of $M_{Q_T}$, it gives

$$E_T=\sum_{i=1}^r(-1)^{i-1}\binom ri m_{\le Y_T}^{*i}*R_{m,i-1,Q_T}.$$

The small-factor mass is at most $2^iY_T^{i/2}$. The filter has mass at most $T^{i\eta}$ and maximum shift $i\log Q_T$. For every remaining argument $s$ in the $i$th forward kernel and every $t\in I_T$,

$$s\ge T-C\log T-i\log Y_T-i\log Q_T
\ge(K-C-r\eta)\log T.$$

The last inequality follows because $Y_T>1$ and $i\le r$, with the smallest available argument at the last stage; equivalently expand the displayed quantities and compare them directly. Apply Q2 with $\ell=i-1$. Since $i\le r$, its exponent is at least $T^p$. Taking the smallest of the finitely many fixed constants and bounding $Y_T^{i/2}\le e^{T/2}$ proves (Q3.4). Causality yields the total product bound; dividing by the other $r-1$ factors, each larger than $Y_T$, gives $Z_T$. $\square$

### 3.2 A concrete fixed-source instance

Choose

$$\boxed{r=2,\quad m=1,\quad C=2,\quad Q_T=1,\quad K=8.}$$

The source is the fixed literal differential image $j_1=Pj$, not an adjustable family. The two factors lie in

$$
\boxed{e^{T/2}T^{-4}<n_1,n_2\le e^{T/2-g}T^4,}
$$

and

$$\|E_T\|_\infty\le C_1\exp(T/2-cT^{3/2}).$$

This replaces the former fixed exponential balance width by a polynomial-in-$T$ width. Since the physical integer scale is $X=e^T$, these are powers of $\log X$ around $X^{1/2}$. No unknown zero location appears in the schedule.

The order $m=1$ is enough for the actual Type I kernels. It is not the stronger order needed for every unrelated coefficient-one stress test. Those are distinct statements.

### 3.3 High-mask transfer on this schedule

Use the true primitive mask and $B(t)=e^{\sqrt t}$. With $r,m$ fixed and $Q_T\le T^\eta$, the two versions of the low-mask bound have the upper budget

$$\log(1+\mathscr K_{2r-1})\le\sqrt T+O_{r,m,\eta,C}(\log T),$$

and the corresponding absorbed-kernel version has the same zero exponential rate. The Type I norm is bounded by $\sqrt{C\log T}\|E_T\|_\infty$.

Round 1's norm-first comparison therefore proves

$$
\frac{\log(1+[\mathcal Q_{B,Q_T}(c_r,c_r)]_+)}{2T}
-
\frac{\log(1+\int_{I_T}|F_m|^2)}{2T}\longrightarrow0.
\tag{Q3.5}
$$

Using the **separate fixed-source PAPER theorem J5.2**, the first expression has limit $\Theta$. MS1 is not needed for this fixed-order construction. Both masks must be priced if free integer factors are absorbed into $R$; the field identity alone does not preserve the mask.

This is a preparatory native arithmetic theorem, not an opposing upper. The balanced signed form retains the full target rate. The unsigned tuple bound still gives the scale $e^{T/2+o(T)}$ for its norm, and writing it as two factors does not divide that exponent by two. The work remaining is a signed estimate on this more tightly specified region.

## R2 4. O1--O2: source-aware recovery with its complete cost

A contrast may lose the coherent observation but leave a source-history channel that recovers it. OPICA must check both information and cost.

### 4.1 Theorem O1: exact constrained recovery

Let $V,W,U$ be finite-dimensional complex Hilbert spaces; let $P:V\to W$, $C:V\to U$ and $\ell:V\to\mathbb C$ be linear. There exists a linear $R$ on the range of

$$A:V\to W\oplus U,\qquad Ax=(Px,Cx),$$

such that $\ell=RA$ if and only if

$$\boxed{\ker P\cap\ker C\subseteq\ker\ell.}\tag{O1.1}$$

When it exists, its exact smallest recovery norm is

$$
\boxed{\kappa_A=
\sup_{Ax\ne0}\frac{|\ell(x)|}{\|Ax\|}<\infty.}
\tag{O1.2}
$$

When $A=0$ and $\ell=0$, the supremum in (O1.2) is defined as zero and the zero recovery map is used. Otherwise its indexing set is nonempty.

**Proof.** Necessity is immediate. Conversely, set $R(Ax)=\ell(x)$. Equation (O1.1) makes this independent of the preimage. Its norm is exactly (O1.2). Extend it by zero on $(\operatorname{Ran}A)^\perp$ without increasing that norm. $\square$

For an affine source class $Cx=b$, the same recovery reads $\ell(x)=R(Px,b)$. The known history is retained, not assumed to be negligible. An affine origin shift $x_0$ can equivalently reduce this to the homogeneous kernel of $C$.

### 4.2 Theorem O2: noisy recovery and rate budgets

If the measured vector $y$ satisfies $\|y-Ax\|\le\varepsilon$, then

$$\boxed{|\ell(x)-Ry|\le\kappa_A\varepsilon.}\tag{O2.1}$$

Thus a family of exact recovery maps can be used on a schedule only after pricing $\kappa_{A_n}$ and every observation/history error. For example, $\log(1+\kappa_{A_n})=o(T_n)$ and $\log(1+\varepsilon_n)=o(T_n)$ make the scalar recovery error subexponential. To transfer a positive target rate, one must also retain the target in the measured data; smallness of a contrast alone is still insufficient.

A sharp elementary control is $P=I-uu^*$ for a unit vector $u$, $Cx=\epsilon\langle u,x\rangle$, and $\ell(x)=\langle u,x\rangle$. Algebraic recovery exists for every $\epsilon\ne0$, but its optimum norm is $1/|\epsilon|$. Choosing $\epsilon=e^{-aT}$ incurs positive exponential cost. Injectivity at each finite stage is not a uniform observation theorem.

The compatibility test has an equally explicit error version. For $B:\mathbb C^d\to\mathbb C^N$, there exists $\alpha$ with $\|b-B\alpha\|\le\varepsilon$ exactly when $\operatorname{dist}(b,\operatorname{Ran}B)\le\varepsilon$. A unit left-annihilator $y$ with $|y^*b|>\varepsilon$ certifies incompatibility. This follows from finite-dimensional orthogonal projection. Counting rows does not construct that certificate.

## R2 5. J1: robust local jets, including changing completion depth

Let a corrected native transform at stage $n$ have coefficient $a_{j_n,n}\ne0$ at degree $j_n\ge-1$ in its Laurent expansion around $\lambda$. On a common circle $|z-\lambda|=r>0$, suppose an approximation has meromorphic error $e_n$ with no other interior pole and

$$\sup_{|z-\lambda|=r}|e_n(z)|\le E_n.$$

### Theorem J1

The error in that Laurent coefficient satisfies

$$\boxed{|\Delta a_{j_n,n}|\le r^{-j_n}E_n.}\tag{J1.1}$$

In particular, the observed coefficient cannot vanish if

$$E_n<|a_{j_n,n}|r^{j_n}.\tag{J1.2}$$

For repeated native completions, $j_n=p_nm-1$ and the true coefficient is the explicit NB1 coefficient, not its unnormalized derivative. Its amplitude, $r^{-j_n}$ and all affine corrections must be priced together.

**Proof.** The Laurent coefficient is the contour integral of $e_n(z)/(z-\lambda)^{j_n+1}$ divided by $2\pi i$. Its length estimate is exactly (J1.1). The reverse triangle inequality proves (J1.2). Equality is sharp: the perturbation $-a_{j_n,n}(z-\lambda)^{j_n}$ cancels the coefficient and has circle norm $|a_{j_n,n}|r^{j_n}$. $\square$

For $j=-1$ this is the residue bound $rE$. For nonnegative $j$, the derivative error is $j!r^{-j}E$. A proof that controls only compact time intervals, a distant convergence half-plane, or an unrelated norm does not supply this circle budget.

This gives a completed finite-to-infinite interface for the displayed local observations. It is not an assertion that the actual approximation errors satisfy it. Coupling this result with NB1 and O2 gives a concrete native preservation test: the true corrected coefficient survives whenever the full perturbation/recovery budget is strictly below its actual value. The condition is not replaced by the words “small error.”

## R2 6. Audit of the renormalized co-Poisson family

Round 1 CP1 defines, for $t\ge0$,

$$
D_t=e^{t/2}\sum_{n\in\mathbb Z}\delta_{e^t n},\qquad
A_t=D_t-e^{t/2}\delta_0,
$$

$$K_t=A_t+\mathcal F A_t
=D_t+D_{-t}-e^{t/2}(\delta_0+dx).$$

The integral $V_\lambda=\int_0^\infty e^{-\lambda t}K_tdt$ is an entire tempered-distribution-valued family on Schwartz tests. The summands' total variations are not integrable; the subtraction is made first. For $\rho=1/2+\lambda$, $0<\Re\rho<1$, its actual order-zero measure representation is

$$
V_\lambda=\rho^{-1}\delta_0+
\left[S_\rho(|x|)+\zeta(\rho)|x|^{\rho-1}+(1-\rho)^{-1}\right]dx,
\tag{6.1}
$$

where, on $x>0$,

$$
S_\rho(x)=x^{-\rho}\sum_{n\le x}n^{\rho-1}
-x^{\rho-1}\sum_{n\le x}n^{-\rho}.
\tag{6.2}
$$

The power near zero is locally integrable. Round 1 proves local total-variation convergence of cutoff measures to (6.1), identifying it with the independently constructed distributional limit. This proof was rechecked; no replacement of the divergent series $\sum n^{-\rho}$ by a convergent one is used.

Set

$$\lambda=\rho-\tfrac12,\quad
\kappa=\rho(1-\rho)=\tfrac14-\lambda^2,\quad
b_\rho=\frac1\rho-\frac1{1-\rho}=-\frac{2\lambda}{\kappa}.$$

For $\rho\ne1/2$, normalize the entire-distribution construction locally by $b_\rho$ and subtract its origin/continuum terms. The result is the self-dual complex measure

$$
\mathcal V_\rho=
\left[\frac{S_\rho(|x|)}{b_\rho}+
\frac{\zeta(\rho)}{b_\rho}|x|^{\rho-1}\right]dx
-\sum_{n\ne0}\delta_n.
\tag{6.3}
$$

At an actual zero, the additional power vanishes. Denote the resulting measure by $\nu_\kappa$, and its density by

$$g_\kappa(x)=S_\rho(|x|)/b_\rho.$$

The reflection $\rho\mapsto1-\rho$ negates both $S_\rho$ and $b_\rho$, so $g_\kappa$ depends on $\kappa$, not on the choice of reflected representative. The parameter $\kappa$ is not the contact probe kernel or the completion.

The real measure in Round 1 is $\Re\nu_\kappa$. The new work below retains complex profiles until a real measure is explicitly selected. All normalized zero-family statements keep $0<\Re\rho<1$, $\rho\ne1/2$, hence $\kappa\ne0$. The exceptional real point is not a nontrivial zero: on $0<s<1$, the paired alternating series for $\eta(s)$ is strictly positive, whereas $1-2^{1-s}<0$, so $\zeta(s)=\eta(s)/(1-2^{1-s})<0$.

## R2 7. S1: the actual zero profile, its jumps, and the retained forcing

### 7.1 Theorem S1a: stronger tail and regularity

For an actual nontrivial zero $\rho$ in the strip, put

$$h_\kappa(x)=1-g_\kappa(x).$$

Then $h_\kappa$ is an even continuous function, equals 1 on $[-1,1]$, belongs to $L^1(\mathbb R)\cap L^2(\mathbb R)$, is Fourier self-dual, and satisfies

$$\int_0^\infty h_\kappa(x)dx=\tfrac12.$$

As $x\to\infty$,

$$
\boxed{
 h_\kappa(x)=\frac{\kappa}{2x^2}B_2(\{x\})+O_\rho(x^{-3}),
 \qquad h_\kappa'(x)=O_\rho(x^{-2})
}
\tag{S1.1}
$$

between integer endpoints. The derivative bound is obtained from the exact differentiated finite sums, not from differentiating an unspecified big-O remainder. The one-sided derivatives obey

$$\boxed{h_\kappa'(n+)-h_\kappa'(n-)=-\kappa/n^2,\qquad n\ge1,}\tag{S1.2}$$

where $h'(1-)=0$. In particular $xh_\kappa'\in L^2(0,\infty)$.

**Proof.** The finite sums in (6.2) vanish for $0<x<1$. At every integer, the two newly entering values both equal $1/n$ and cancel, so $S_\rho$ is continuous. Their derivatives differ by $(1-2\rho)/n^2$. Division by $b_\rho$ gives the jump $\kappa/n^2$ for $g$, hence (S1.2) for $h$.

A two-step Euler--Maclaurin expansion, with one further bounded-periodic remainder integration, gives, uniformly across real cutoffs and with the right endpoint convention,

$$
\sum_{n\le x}n^{-s}
=\zeta(s)+\frac{x^{1-s}}{1-s}
-B_1(\{x\})x^{-s}-\frac{s}{2}B_2(\{x\})x^{-s-1}
+O_s(x^{-\Re s-2}).
\tag{S1.3}
$$

Use $B_1(u)=u-1/2$, with its right endpoint value at integers, and $B_2(u)=u^2-u+1/6$. This formula is an Euler--Maclaurin statement about finite sums, not a convergent Dirichlet series in the strip.

Apply it at $s=\rho$ and $s=1-\rho$. The functional equation gives $\zeta(1-\rho)=0$. The two $B_1/x$ terms cancel, and

$$S_\rho(x)=b_\rho+\frac{2\rho-1}{2x^2}B_2(\{x\})+O_\rho(x^{-3}).$$

Since $(2\rho-1)/b_\rho=-\kappa$, this proves the first formula. Differentiating the exact finite sums within each cell and inserting (S1.3) gives the derivative bound. It is also locally bounded away from the specified jumps. The resulting tail bounds prove the integrability assertions and absolute convergence of $\sum_{n\ge1}h_\kappa(n)$.

The identity

$$\nu_\kappa=(dx+\delta_0-D_0)-h_\kappa(x)dx$$

shows that $h_\kappa dx$ is self-dual, because both other distributions are. Since $h_\kappa\in L^1$ and is continuous, this is the ordinary Fourier identity. Evaluation at zero gives $\int_{\mathbb R}h_\kappa=h_\kappa(0)=1$; evenness gives the half-line integral. $\square$

### 7.2 Theorem S1b: exact Euler equation

On $(0,\infty)$, in distributions,

$$
\boxed{
-\frac d{dx}\left(x^2h_\kappa'(x)\right)
=\kappa\left(h_\kappa(x)-1+\sum_{n\ge1}\delta_n\right).
}
\tag{S1.4}
$$

**Proof.** Inside each cell, $g$ is a combination of $x^{-\rho}$ and $x^{\rho-1}$, whose Euler exponents solve $a(a+1)+\kappa=0$. Therefore $(x^2g')'+\kappa g=0$. Substituting $h=1-g$ gives the ordinary part of (S1.4). The jump in $x^2h'$ is $-\kappa$ at every positive integer, so its negative derivative adds precisely $\kappa\delta_n$. Continuity ensures that no derivative of a delta appears. $\square$

This is not $Lh=\kappa h$. It contains the actual nonzero lattice-minus-continuum force

$$\kappa\left(\sum_{n\ge1}\delta_n-dx\right).$$

Although $h$ lies in the quadratic-form domain of $L=-\partial_x(x^2\partial_x)$, its distributional image contains atoms and is not an $L^2$ function. Thus it is not in the operator domain of the usual $L^2$ self-adjoint realization with this differential expression. Treating it as an eigenfunction deletes the very arithmetic terms retained by the construction.

The unitary change $x=e^t$, $\psi(t)=e^{t/2}h(e^t)$ gives the independent positive form identity

$$
\int_0^\infty x^2|h'|^2dx
=\int_{\mathbb R}|\psi'|^2dt+\frac14\int_0^\infty|h|^2dx.
\tag{S1.5}
$$

It does not make the forced equation homogeneous.

## R2 8. S2: an exact native multi-zero sampling compatibility law

For any finite set of actual zeros, choose one representative for each distinct $\kappa_i=\rho_i(1-\rho_i)$. Define

$$
N_{ij}=\int_0^\infty h_{\kappa_i}(x)\overline{h_{\kappa_j}(x)}dx,
\quad
Q_{ij}=\int_0^\infty x^2h_{\kappa_i}'(x)\overline{h_{\kappa_j}'(x)}dx,
$$

$$S_i=\sum_{n\ge1}h_{\kappa_i}(n),\qquad b_i=S_i-\tfrac12.$$

All integrals and sums converge absolutely in the required sense by S1. The inner-product convention in this section is linear in the first argument.

### Theorem S2

Both $N$ and $Q$ are positive semidefinite Hermitian Gram matrices, and

$$
\boxed{
Q_{ij}=\kappa_i(N_{ij}+\overline{b_j})
=\overline{\kappa_j}(N_{ij}+b_i).
}
\tag{S2.1}
$$

Consequently,

$$
(\kappa_i-\overline{\kappa_j})N_{ij}
=\overline{\kappa_j}b_i-\kappa_i\overline{b_j}.
\tag{S2.2}
$$

When the denominator is nonzero and $M_i=b_i/\kappa_i$,

$$
\boxed{
\frac{N_{ij}}{\kappa_i\overline{\kappa_j}}
=\frac{M_i-\overline{M_j}}{\kappa_i-\overline{\kappa_j}}.
}
\tag{S2.3}
$$

In particular, when $\Im\kappa_i\ne0$,

$$\boxed{\frac{\Im M_i}{\Im\kappa_i}=\frac{N_{ii}}{|\kappa_i|^2}>0.}\tag{S2.4}$$

**Proof.** Pair (S1.4) with $\overline{h_{\kappa_j}}$ on a finite union of cells, including every derivative jump. The boundary at zero vanishes because $h$ is constant there. Choose endpoints tending to infinity away from the integers. By S1, $x^2h_i'\overline{h_j}=O(x^{-2})$, so the outer boundary vanishes. The continuum term has integral $1/2$ and the atomic term has the absolutely convergent sum $\overline{S_j}$. This proves the first equality in (S2.1). Hermitian symmetry gives the second. Algebra gives (S2.2)--(S2.4). Finally $N_{ii}>0$ because $h_i=1$ on $(0,1)$. $\square$

Equation (S2.2), not the divided expression, is retained when parameters coincide under conjugation. Critical-line parameters are real; no division by their zero imaginary part is permitted. A finite collection in one open half-plane of the $\kappa$ plane gives a positive semidefinite divided-difference matrix through (S2.3). No uniform conditioning bound for changing zero sets is inferred.

The positive form identity also gives the matrix inequality $Q-\tfrac14N\succeq0$: apply (S1.5) to each finite linear combination. This supplies an additional exact form constraint, not a claim that the forcing is absent.

This is a coupled constraint on actual zero-generated profiles, beyond merely counting equations against a finite history. It still does not exclude an off-line zero. The sampling values $S_i$ have not been independently bounded or shown real. They are exactly the arithmetic part that a false self-adjoint eigenvalue argument omits.

#### A falsification of the automatic spectral-exclusion inference

Take any positive real diagonal matrix $A$, a nonzero real vector $g$, and nonreal parameters $\kappa_i$. Let

$$h_i=\kappa_i(A-\kappa_i I)^{-1}g,\qquad b_i=g^*h_i.$$

The same algebraic identities (S2.1)--(S2.3) hold with $N_{ij}=\langle h_i,h_j\rangle$ and $Q_{ij}=\langle Ah_i,h_j\rangle$. Nonreal parameters are entirely compatible with these positive Gram matrices because the equation is forced. This is an auxiliary finite-dimensional control, not a second genuine zeta system. It rejects only the inference from positivity and the displayed identities to reality of the parameters.

An additional source-sensitive fact about the actual $S_i$ might still matter. No such independent opposing fact is supplied here.

## R2 9. H1--H2: every finite multiplicity-sensitive co-Poisson combination is tested

### 9.1 Theorem H1: actual zero jets remain measures with the exact gap

Let $\rho_j$ be actual zeros of multiplicities $m_j$, with distinct parameters $\kappa_j=\rho_j(1-\rho_j)$. Locally choose the holomorphic inverse branch $\rho=\rho(\kappa)$; this is possible because $1-2\rho_j\ne0$. For $0\le k<m_j$, define

$$\nu_{j,k}=\frac1{k!}\left.\partial_\kappa^k\mathcal V_{\rho(\kappa)}\right|_{\kappa_j}.$$

Then each $\nu_{j,k}$ is an even Fourier-self-dual complex order-zero measure, has the exact open unit gap and zero origin atom, and has linear total-variation growth. Explicitly,

$$
\nu_{j,k}
=\frac1{k!}\left.\partial_\kappa^k g_\kappa(|x|)\right|_{\kappa_j}dx
-\mathbf1_{k=0}\sum_{n\ne0}\delta_n.
\tag{H1.1}
$$

**Proof.** On compact parameter disks inside $0<\Re\rho<1$, the cutoff construction and its derivatives converge on Schwartz tests. The explicit formula (6.3) identifies locally integrable density derivatives; powers of $\log|x|$ near zero remain integrable on a compact substrip. The term $\zeta(\rho(\kappa))|x|^{\rho(\kappa)-1}/b_{\rho(\kappa)}$ vanishes through order $m_j-1$ at $\kappa_j$. It therefore contributes neither an interior-gap density nor an origin atom to the displayed jets.

Euler--Maclaurin is locally uniform in the same parameter disk. The functional equation gives the reflected zero with the same multiplicity. Differentiating the expansion before specializing to the zero shows that the zeroth density is $1+O(x^{-2})$ and each higher density is $O(x^{-2})$, with fixed jet-dependent constants. The potentially slower zeta-tail terms and their derivatives through the relevant order vanish. This proves linear variation growth and validates order-zero measure status. Fourier self-duality passes through parameter differentiation on Schwartz tests. $\square$

Multiplicity is used here to obtain the extra jets, not assumed to be one. Derivatives beyond the actual multiplicity need not retain the gap.

The multiplicity derivatives also retain their source term. Put $G=\sum_{n\ge1}\delta_n-dx$ and $h_{j,k}=(1/k!)\partial_\kappa^kh_\kappa|_{\kappa_j}$. Differentiating the exact distributional equation before specializing gives

$$
\begin{aligned}
(L-\kappa_j)h_{j,0}&=\kappa_jG,\\
(L-\kappa_j)h_{j,1}&=h_{j,0}+G,\\
(L-\kappa_j)h_{j,k}&=h_{j,k-1}\quad(k\ge2),
\end{aligned}
\tag{H1.2}
$$

Only existing derivatives $k<m_j$ are claimed in the gapped measure family. This is a forced chain, not a homogeneous generalized-eigenvector chain. The same finite-cell formula defines an analytic $h_\kappa$ before imposing any zero equation, so the displayed differentiation is legitimate locally in the parameter; the zero multiplicity is what supplies the global decay and gap of the selected jets.

### 9.2 Theorem H2a: finite independence, with reflection removed correctly

The measures $\nu_{j,k}$ for $0\le k<m_j$ are complex-linearly independent.

**Proof.** On $1<x<2$, put $u=\log x$. The density has the entire right-cell expression

$$
e^{u/2}g_\kappa(e^u)
=\kappa\frac{\sinh(\sqrt{1/4-\kappa}\,u)}{\sqrt{1/4-\kappa}}
=\kappa\sum_{n\ge0}\frac{(1/4-\kappa)^n u^{2n+1}}{(2n+1)!}.
\tag{H2.1}
$$

The power series removes any square-root-branch ambiguity. Let $M=\sum_jm_j$. If a linear combination of the measures is zero, its analytic density vanishes on this first interval. Its first $M$ odd Taylor coefficients at $u=0$ therefore give the homogeneous system whose matrix is

$$\frac1{k!}\left.\partial_\kappa^k[\kappa(1/4-\kappa)^n]\right|_{\kappa_j},
\qquad 0\le n<M.$$

This matrix is invertible. The polynomials $(1/4-\kappa)^n$ span all degrees below $M$; Hermite evaluation at distinct nodes with total multiplicity $M$ is invertible. Multiplication by $\kappa$ acts invertibly on every truncated local jet because $\kappa_j\ne0$. Hence every coefficient is zero. $\square$

For the order with columns $(j,0),(j,1),\ldots,(j,m_j-1)$ at each node, the matrix just used has the exact determinant

$$
\boxed{
\det A=(-1)^{M(M-1)/2}
\left(\prod_j\kappa_j^{m_j}\right)
\left(\prod_{i<j}(\kappa_j-\kappa_i)^{m_im_j}\right).
}
\tag{H2.3}
$$

Indeed the triangular change from monomials to $(1/4-\kappa)^n$ has determinant $\prod_{n=0}^{M-1}(-1)^n$; the normalized Hermite matrix has the confluent Vandermonde determinant; multiplying by $\kappa$ on each local jet block contributes $\kappa_j^{m_j}$. No derivative factorial is missing because the jet columns use $1/k!$. This formula provides exact finite independence but does not give a uniform inverse norm under collisions.

The parameters for $\rho$ and $1-\rho$ are identical and must not be counted as separate nodes. Conjugate nodes are kept with their actual conjugation relation when real measures are formed.

### 9.3 Theorem H2b: no nonzero real finite combination enters the positive cone

Take any real measure formed from a finite collection in H1, pairing conjugate nodes and coefficients correctly. If it is nonnegative off the integer lattice, it is zero, and H2a then forces all its independent real coefficients to vanish.

**Proof.** Every member of the finite span has the exact gap, origin, growth and self-duality properties required by the signed sharp-gap separator. The separator gives zero. H2a provides nontriviality for nonzero coefficient data rather than assuming it. $\square$

This closes the proposed finite multi-zero linear repair for this family, including all available multiplicity jets. It does not classify arbitrary nonlinear maps, infinite non-controlled combinations, or every contact-to-measure construction.

For a fixed finite independent real basis $\omega_1,\ldots,\omega_d$ of this span, there is also a strictly positive constant $c_\omega$ such that

$$
\boxed{
\int_{\mathbb R\setminus\mathbb Z}s(x)\,d(\nu_a)_-(x)
\ge c_\omega\|a\|_2,\quad
\nu_a=\sum_{j=1}^da_j\omega_j,\quad
s(x)=\left(\frac{\sin\pi x}{\pi x}\right)^2.
}
\tag{H2.2}
$$

To prove this, the weighted negative-mass functional is continuous in the finite coefficient vector: the weighted variation norm is finite for every basis measure and controls the variation of the negative part. It is positive on every nonzero vector by H2b and the exact pairing $\int s\,d\nu=0$. Minimize it on the compact Euclidean unit sphere and use positive homogeneity. The constant depends on the entire finite system. No uniform constant for clustered or growing sets of zeros is claimed.

## R2 10. H3: an explicit correction cost in the first lattice interval

For the normalized real single-zero measure from Round 1, let $\lambda=\delta+i\gamma$, $|\delta|<1/2$ and $|\gamma|\ge16$. Put

$$u_1=\frac{4\pi}{3|\gamma|},\qquad u_2=\frac{5\pi}{3|\gamma|},\qquad J_\gamma=[e^{u_1},e^{u_2}].$$

### Theorem H3

Its off-lattice density satisfies

$$f_\rho(e^u)\le-\frac{|\gamma|}{2}e^{-u/2}\quad(u_1\le u\le u_2),$$

and consequently

$$
\boxed{
\int_{J_\gamma}(-f_\rho)_+dx\ge\frac\pi6,\qquad
\int_{J_\gamma}s(x)(-f_\rho)_+dx\ge\frac{8\pi}{27\gamma^2}.
}
\tag{H3.1}
$$

**Proof.** Take $\gamma>0$ by conjugation. The first-cell formula gives

$$f_\rho(e^u)=e^{-u/2}\left[
A\sinh(\delta u)\cos(\gamma u)
+\gamma\left(1+\frac1{4(\delta^2+\gamma^2)}\right)
\cosh(\delta u)\sin(\gamma u)\right],$$

where $A=\delta[(4(\delta^2+\gamma^2))^{-1}-1]$ and $|A|\le1/2$. On the selected interval, $\sin(\gamma u)\le-\sqrt3/2<-3/4$ and $|\cos(\gamma u)|\le1/2$. Also $e^{u_2}<3/2$: use $5\pi/48<1/3\le\log(3/2)$. The hyperbolic small term has absolute value less than $1/8$: $|\delta u|\le1/6$, and the power series gives $\sinh(1/6)\le(1/6)/(1-1/36)=6/35$, so that term is at most $3/70$. The claimed negative bound follows, with ample margin at $\gamma\ge16$.

Since $dx=e^u du$, the unweighted negative mass is at least $(\gamma/2)(u_2-u_1)=\pi/6$. On this interval, $1<x<3/2$, so $\operatorname{dist}(x,\mathbb Z)=x-1\ge u_1$ and $x\le2$. The elementary sinc bound gives $s(x)\ge u_1^2/\pi^2=16/(9\gamma^2)$. Multiply the two bounds. $\square$

Any signed correction making this particular density nonnegative on $J_\gamma$ must add positive variation at least $\pi/6$ there. A lattice-supported correction has no effect. The height assumption is part of the theorem; this paper makes no unstated numerical assertion that every zero meets it. The theorem also applies when $\delta=0$, so it is not an off-line-zero exclusion.

## R2 11. S3: a nonlinear square repairs the sign but has a nonremovable duality defect

The preceding results exclude finite linear repairs within the zero-jet family. A different candidate is to square its gapped function, obtaining positivity directly.

Let $h\in L^1\cap L^2$ be an even continuous Fourier-self-dual function, vanishing at infinity, and suppose $h=A$ on $[-1,1]$ for a complex constant $A$. Put $f=A-h$, and define

$$\tau_h=|f(x)|^2dx-|A|^2\sum_{n\ne0}\delta_n.$$

For the actual zero profile use $h=h_\kappa$, $A=1$. Finite real or complex combinations of those profiles also fit with the appropriate $A$.

### Theorem S3

The measure $\tau_h$ has zero origin atom, exact open unit gap, nonnegative off-lattice density, and linear variation growth. Its Fourier defect is the continuous function vanishing at infinity

$$
\boxed{\mathcal F\tau_h-\tau_h=
\left(h*\overline h-|h|^2\right)dx.}
\tag{S3.1}
$$

At zero this defect has value

$$
\boxed{\|h\|_2^2-|A|^2.}\tag{S3.2}
$$

If $A\ne0$, it is at least $|A|^2>0$, since $h=A$ on an interval of length two. If $A=0$ and $h\ne0$, it is also strictly positive. Thus the nonzero square construction is not self-dual.

Moreover, no tempered lattice-supported measure $\sigma$ can repair this defect: $\tau_h+\sigma$ cannot be self-dual when (S3.2) is nonzero.

**Proof.** The sign, gap and growth follow directly from the definition and boundedness of $h$. Fourier transformation of

$$|A-h|^2=|A|^2-\overline A h-A\overline h+|h|^2$$

preserves the two linear terms. Since $h$ is even and self-dual, so is $\overline h$; the product transform is $h*\overline h$. The constant and comb terms interchange with the exact matching origin terms. Subtraction yields (S3.1). The convolution is continuous and vanishes at infinity (equivalently it is the Fourier transform of $|h|^2\in L^1$); so does $|h|^2$. Evenness gives $(h*\overline h)(0)=\|h\|_2^2$, proving (S3.2).

For the correction claim, write the continuous $C_0$ defect as $d(x)$. If $\mathcal F\sigma-\sigma=-d(x)dx$, then $\mathcal F\sigma$ is 1-periodic because $\sigma$ is supported on the integers. Translating the equation by one gives a lattice-supported distribution equal to the continuous density $d(x+1)-d(x)$. Such a distribution is zero: the continuous density vanishes off the lattice, hence everywhere, and its atomic counterpart also vanishes. Thus $d$ is 1-periodic. A continuous periodic function tending to zero at infinity is zero, contradicting (S3.2). $\square$

The exact self-dual projection also has a priced failure. Since $\mathcal Fd=-d$,

$$
\tau_h^+=\tfrac12(\tau_h+\mathcal F\tau_h)=\tau_h+\tfrac12d(x)dx
\tag{S3.3}
$$

is self-dual. But on $(-1,1)$, where $\tau_h=0$, its density is $d/2$, which is strictly positive near zero by (S3.2) and continuity. Symmetrizing the square therefore fills the very gap needed by the separator. This conclusion is local and exact; no numerical test or omitted tail is involved. The projection need not remain nonnegative everywhere else, and no such claim is made.

This candidate genuinely repairs the missing sign, but it cannot retain duality. The failure is measured at one finite spatial point, not inferred from a slogan that nonlinear operations are forbidden. The theorem applies to the displayed square family only; it does not rule out every nonlinear source construction.

## R2 15. Sources and reproducibility

### Project sources

**P0.** `OPICA_Paper_Construction_v1_0_2026-10-21.md`, especially local laws L1--L5, arithmetic A1--A3, observation O1--O4, and signed separator H1. Its original paper status is retained.

**P1.** `OPICA_Beyond_PR_Research_Round1_2026-10-21.md`: NB1, AT1--AT2, HT1--HT2, CT1, MC1, CP1. Its full source and executed checker are included. [Verified Drive source](https://drive.google.com/file/d/1M_EmuJczExFmIA5IN51sOCN8xaF0rUl6/view).

**P2.** Original M0659, `continuation_native_j.md`, 18 October 2026: actual one-$Q$ source, fixed-order rapid forward kernels, J17 decomposition, J5.2, and the genuinely open signed estimate. Physical handover navigation approximately 8768--8781. Preserved source body included.

**P3.** Original M1196, `round4_energy.md`: auxiliary completion and logarithmic-window proof. Preserved source body included; not formalized anew.

**P4.** *Divisor-Controlled Mask Transfer and Moving-Source Continuation*, 20 October 2026: DC1/DC2 and MS1. The preserved export is included. [Source document](https://docs.google.com/document/d/1KcUovuIEsqhmJ25Yqn3U-ItDmLVEVRJx-_Ltpp_CYTA/edit).

**P5.** A03 first-drive Poisson localization and M0608's later source-correct use, as retrieved from `RH_Step4_Third_Party_Complete_Handover.pdf`. The first-drive double-exponential scale is inherited, not claimed new.

**P6.** Fresh main reference and visible open-PR list, `HMarcusWH/zeta-23-lean`, 21 October 2026. Observed main `97926d6a949fed7af0429a373b47abc772012834`. No new tree/CI certification.

### External primary formula sources and context

**E1.** NIST DLMF 25.4.2, zeta reflection formula: <https://dlmf.nist.gov/25.4.E2>. Used in Q1b. Formula recalled with proof-domain assumptions in the text, not a new native zero-free theorem.

**E2.** NIST DLMF 5.11, gamma asymptotics and uniform strip estimates: <https://dlmf.nist.gov/5.11>. Used with the exact recurrence to price the moving left line. Only a fixed base gamma strip needs the classical asymptotic bound.

**E3.** NIST DLMF 25.11(iii), finite sums/Hurwitz Euler--Maclaurin representations: <https://dlmf.nist.gov/25.11>. Used for the explicitly derived expansion S1.3 and its locally uniform parameter version.

**E4.** Jean-François Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta function*, JTNB 16 (2004), 65--94, DOI 10.5802/jtnb.434. [Primary publication](https://numdam.org/articles/10.5802/jtnb.434/). Relevant context for co-Poisson/Sonine/zero systems; no general novelty claim and no theorem silently imported as a native closing estimate.

The main derivations are written in this document. The copied inputs, exact checker and receipts are hashed in the package. Temporary authenticated download links are excluded. The normal and optimized exact-check commands and numerical command are in `README.md`.

# VI. End-to-end audit decisions and follow-up acceptance

## VI.1 Per-statement audit outcome

The audit ledger covers all eight Round 1 groups and fifteen Round 2 statements. It distinguishes checked proof steps from assumed external classical theorems and from unfinished native research. The three F-statements in Part III are new source-identification/representation results at PAPER authority. The fixed/moving window argument in Part II is an expanded audit of inherited mathematics, not three extra sources of formal authority.

| Result family | Audit conclusion |
|---|---|
| R1-NB1 | Concrete native multipliers have the stated local orders; analytic histories must remain in the correction ledger. No global norm conclusion follows from local units. |
| R1-AT1, AT2 | Norm-first logarithmic comparison and allocation hold for complex Hilbert fields. The signed high form uses its positive part, not PSD status. |
| R1-HT1 | Noncompact inversion is justified only at an exponential moment strictly above $1/2$. The critical endpoint and renormalized families remain outside this class. |
| R1-HT2, CT1 | Common variation bounds preserve the measure limit; normalization in the explicit control destroys them and leaves delta derivatives. |
| R1-MC1 | Exact coupled data remove the putative conditioning blow-up in the stated rational model. This is not a claim about actual zero collisions. |
| R1-CP1 | Subtract first, prove local variation convergence, then identify the measure. Scalar sign/phase controls are exact in their stated height ranges. |
| R2-Q1a, Q1b | Source and gamma/zeta estimates are uniform in the contour index before optimization. Fixed-source constants are not secretly changing with the horizon. |
| R2-Q2 | Contour optimization proves the displayed fixed-order bound. The individual source/convolution/derivative orders remain fixed. |
| R2-Q3 | Real cutoffs, palette delay, repeated-prime tuples and the final causal product constraint are all retained. Both low masks are paid after regrouping. |
| R2-O1, O2 | Recoverability is exact; applying it to noisy data uses the extension to the whole observation space and a nonnegative tolerance. Conditioning can be exponential. |
| R2-J1 | Laurent coefficient estimate is a common-contour statement with positive radius. Unrelated time/transform norms do not supply its premise. |
| R2-S1a, S1b | Finite-sum Euler--Maclaurin, derivative jumps and all lattice force terms agree. Form-domain membership is not homogeneous operator-domain membership. |
| R2-S2 | Conjugations and the undivided identity are correct. Part III computes the actual sampling term without assuming it real. |
| R2-H1 | Only derivatives below the actual zero multiplicity retain the exact gap. Parameter and spatial derivatives are distinct. |
| R2-H2a, H2b | Reflection-duplicate parameters are removed; normalized confluent determinant and fixed-span separation are valid. No uniform frame constant is supplied. |
| R2-H3 | The height condition is retained; the first-cell bounds imply the stated negative mass. They also apply on the critical line. |
| R2-S3 | The square's defect, its nonzero origin value, lattice-only obstruction and gap-filling projection agree. No assertion about all nonlinear maps follows. |
| Part II / J5.2, MS1 | The source bounds, uniform auxiliary completions, zero multiplicity and memory-to-window arguments compose on the stated schedules. Classical explicit formula/zero count remain named analytic inputs, not new Lean roots. |
| F1--F3 | The arithmetic force is tempered only after subtraction; the actual sample is a Stieltjes transform; the plateau coefficient is exactly the zeta coefficient. This completes the representation, not an exclusion. |

No displayed sign, factorial, reflection identification or end-to-end equality was silently changed. General-mask measurability and common-contour regularity are explicit extra hypotheses of the abstract formulations. All actual masks/contours used in the applications meet them or retain their verification as a stated premise.

## VI.2 The exact independent input still absent

The final arithmetic chain is

$$
\begin{gathered}
\text{literal source and native convolution}\\
\Downarrow\\
\text{fixed-order forward localization}\\
\Downarrow\\
\text{exact logarithmic-slack balanced field}\\
\Downarrow\\
\text{both actual low masks + norm-first transfer}\\
\Downarrow\\
\text{native window theorem}\\
\Downarrow\\
\text{retained observation has rate }\Theta.
\end{gathered}
$$

There is no last arrow to $\Theta=0$ without an independent smaller upper. The completed chain is not labelled a new restriction on the zero location merely because its intermediate arithmetic region is narrower.

The final Fourier/spectral chain is

$$
\begin{gathered}
\text{actual zero and integer-comb construction}\\
\Downarrow\\
\text{legitimate gapped self-dual signed measure}\\
\Downarrow\\
\text{exact sign failures and forced profile}\\
\Downarrow\\
\text{native sampling/Stieltjes identity}.
\end{gathered}
$$

A positive form and a source-derived sampling identity do not force a homogeneous eigenvalue equation. The explicit generic nonreal resolvent in F3 and the forced finite-dimensional controls remain valid falsification checks. The square construction supplies positivity but its calculated Fourier defect is nonzero; no forbidden measure has been constructed.

The programme still needs one genuinely independent input: a signed upper on the complete retained arithmetic, actual-input range membership, the full original Schur upper, an independently incompatible sampling/boundary constraint, or another nonzero native object satisfying every separator hypothesis. This release neither proves one nor asserts it impossible.

## VI.3 What is ready to implement

The follow-up implementation should consume the first OPICA PR at its actual accepted head. The paper does not invent its future module paths or declare its 76 roots compiled. The accompanying final contract defines exact mathematical targets and anti-substitution tests, while leaving path-level wiring for the actual first-PR inventory.

The first priority for implementation is the cheap abstract layer (norm-first comparison, measured recovery and robust contour observation), followed by the native arithmetic source estimate, and then the co-Poisson measure/profile and spectral completion. This is a dependency order, not a claim that the analytic proofs are already available in Mathlib.

No infinite theorem may be replaced by a finite checker, and no native theorem may be replaced by a generic statement assuming the desired native property. In particular, the source-correct explicit formula, source transform inversion, co-Poisson order-zero representation and log-space forcing identity are genuine obligations.

## VI.4 Execution harvest

The existing exact Round 1 and Round 2 checkers were run unchanged under normal and optimized Python. Counts, mathematical group dispositions and script hashes were compared with their frozen receipts. A fresh exact checker tests the finite algebra behind the sampling completion and a separate numerical checker compares the actual generic-parameter resolvent profile to its logarithmic Fourier formula. Generic parameters in these numerical checks are explicitly **not asserted zeta zeros**.

The old and new numerical checks are consistency tests, not interval-certified inequalities. The infinite arguments are the proofs above and in the collected technical parts. No finite result was promoted to an infinite sign, asymptotic or measure-convergence theorem.

The machine-readable final audit receipt records actual counts and all comparison results. It also records two operational retries: an unsupported interactive container-session request, and an initial receipt comparison using the wrong historical hash-field name. Neither was a mathematical failed test; neither is counted as a pass. The corrected ordinary execution and schema-aware comparison are the recorded completed runs.

PDF rendering and full-payload verification check presentation and byte integrity. They do not constitute independent mathematical review. The release contains no font files.

## VI.5 Post-result research pass

**What became formally true:** no new Lean declaration or CI result. The paper-stage proofs and source identifications are the delivered mathematical state.

**Workflow harvest:** all executed local controls and their frozen comparisons are recorded. No first-PR green status was presumed; its final-head harvest remains pending actual source and workflow evidence.

**What changed:** direct analytic dependencies have a complete written proof chain, and the previously symbolic sample term is identified with the genuine zeta spectral measure. The fixed-source arithmetic region remains polynomially balanced with a negligible Type I field.

**Upstream implications:** preserve the distinction between original source, derivative source and heat profile. Keep the forcing as an $H^{-1}$ object before Fourier transformation. The covariance cutoff must be measurable, and the observation must retain its recovery cost.

**Downstream implications:** a future signed arithmetic upper has an exact rate consumer. A future spectral argument can no longer treat the sample sum as an unspecified real scalar; F2 supplies its native value. This may simplify testing proposed constraints.

**Resurrected routes:** a better estimate on the existing linear arithmetic or spectral representation is still legitimate. The proofs do not impose a nonlinear-only research rule. The explicitly excluded scalar/finite-span/lattice-only repairs remain excluded in their stated classes.

**New clues:** the arithmetic and spectral branches now isolate different independent obligations. Neither one is resolved by the other's information-preserving identities. An additional identity is progress only if it supplies an independently useful restriction, not merely a new name for the same observed coefficient.

**Falsification checks:** modified sources, erased signs, loss of boundary jets, unsupported contour passage, incorrect homogeneous eigenvalue equations and incoherent source normalizations remain inadmissible. The new generic resolvent test prices the tail that a finite spatial truncation would otherwise omit.

**Highest-leverage next move:** independent review and formalization of this exact paper package, coupled with research into the actual complete signed bound or boundary-amplitude restriction. Neither task should be replaced by another expansion of the completed preservation catalogue alone.

**Final claim state:** scoped follow-up paper completed and self-audited; formalization and independent review pending; independent exclusion and RH OPEN.

# VII. Global source register and reproducibility

**[S0]** OPICA paper construction v1.0, 21 October 2026. All 25 original statement families are foundational inputs, not recounted as new follow-up discoveries. The full frozen manuscript is included.

**[S1]** OPICA Beyond-PR Round 1, manuscript, eight-group ledger and evidence archive. The technical chapters reproduced in Part IV retain their original source-local labels and references. The complete original is preserved byte-for-byte.

**[S2]** OPICA Beyond-PR Round 2, manuscript, fifteen-statement ledger, contract and evidence archive. The technical chapters reproduced in Part V retain their original source-local labels and references. The complete original is preserved byte-for-byte. **[S2-manifest]** is its original release manifest, which explicitly records the incomplete full research programme.

**[S3]** M0659, `continuation_native_j.md`, 18 October 2026. Actual-source transform, J17 finite identity, source-parametric explicit formula and fixed-source logarithmic-window theorem. PAPER input, not newly compiled.

**[S4]** M1196, `round4_energy.md`, 18 October 2026. Source-independent auxiliary completions, uniform kernel/normalization constants, full multiplicity tail residual, logarithmic-window argument. Its original autocorrelation source is not silently substituted for $j$; Part II uses the source-parametric version with the literal $j_m$ inputs checked separately.

**[S5]** DC/MS continuation, 20 October 2026, exact preserved text export. Divisor-controlled mask estimates and slowly changing source theorem. Its quantitative hypotheses are made explicit in Part II and retained in the ledger.

**[S6]** Fresh GitHub main/open-PR reads for `HMarcusWH/zeta-23-lean`. These establish only the read state, not a new build or whole-tree audit.

**[W1]** NIST DLMF 25.4.2, reflection formula, <https://dlmf.nist.gov/25.4.E2>. Checked as a primary formula reference.

**[W2]** NIST DLMF 5.11, gamma asymptotics and fixed-strip control, <https://dlmf.nist.gov/5.11>. Used together with exact recurrence; Stirling also evaluates the explicitly telescoped sawtooth norm.

**[W3]** NIST DLMF 25.11(iii), Hurwitz/Euler--Maclaurin representations, <https://dlmf.nist.gov/25.11>. The real-cutoff expansion and derivative use are derived with their own endpoint conventions in the paper.

**[W4]** Jean-François Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta function*, JTNB 16 (2004), 65--94, DOI 10.5802/jtnb.434, <https://numdam.org/articles/10.5802/jtnb.434/>. Classical co-Poisson/Sonine/zero-system context; no theorem from that work is silently installed as a Step 4 upper, and no global priority claim is made here.

The combined evidence archive includes the original complete technical sources, the new audit/completion text, executed scripts, results, source hashes, rendered-document QA and a complete payload manifest. The standalone audit report records the exact validation totals and the remaining review boundaries. Temporary authenticated download URLs are not part of the release.
