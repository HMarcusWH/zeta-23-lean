---
title: "OPICA beyond the first PR: quantitative native transport and the co-Poisson boundary"
subtitle: "Second paper tranche, proof audit, and follow-up theorem contract"
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
  - \allowdisplaybreaks
  - \setlength{\emergencystretch}{3em}
---

# 0. Status, objective and exact scope

**Authority: DERIVED / PAPER, with self-audit and separately scoped executable controls.** No new Lean declaration, repository change, CI run, independent referee review, or improved zero-free region is claimed. The first OPICA implementation remains assigned to ChatGPT Work. This document is mathematical work for the subsequent tranche, not a competing implementation.

Local theorem labels in this document carry the prefix **R2** in the accompanying ledger. In particular, R2-H1 is the zero-jet measure theorem; it is not the original paper's signed separator, cited as **P0-H1**.

The original OPICA paper constructs a restricted preservation calculus. Round 1 adds actual native generators, a weaker norm-first arithmetic interface, convergent heat transports, and a renormalized zero-generated signed measure. The present round completes several specific extensions rather than simply repeating that a closing estimate is missing:

* It proves a quantitative double-exponential decay bound for **all the required fixed-order forward integer kernels**, extending the already known first-drive case. This makes a **logarithmic-slack, polynomially balanced inverse decomposition** legal. The source order can stay fixed; there is no free fixed positive balance loss and no need to invoke the moving-source theorem solely to establish this decomposition.
* It completes robust observation and local-jet interfaces: finite history channels, exact optimal recovery cost, measurement errors, correction ledgers, and the contour budget for growing jet orders.
* It extends the co-Poisson construction to finite arbitrary-multiplicity zero jets, proves their finite linear independence modulo the true reflection symmetry, and excludes every nonzero real finite linear combination from the sharp-gap positive cone.
* It calculates an actual self-dual function associated with the zero-generated measure, including its tail, integer jumps, and global energy/sampling identity. The resulting equation is **forced**, not a homogeneous eigenvalue problem. The force is explicitly the unchanged lattice-minus-continuum distribution.
* It tests a genuinely nonlinear repair, squaring the gapped native function. The square has the desired sign and gap, but its Fourier-duality defect is strictly positive at the origin. No lattice-supported correction can remove that defect.

These results close their displayed paper proof obligations. They do **not** complete the independent-exclusion objective of the full OPICA research programme. A-X, B-Y, C-Schur, OPEN-J46 and a nonzero native object satisfying all sharp-gap separator hypotheses remain OPEN. The paper distinguishes a completed theorem package from completion of RH or the entire research programme.

## 0.1 Inputs and what was checked

The complete Round 1 manuscript and its source/check package were read locally and hashed. The Round 1 manuscript hash is

`20090037bbbab5a45c27f2f5665656eff3c6c619fc27ac9860a3b463da537843`.

The fixed-source original `M0659__continuation_native_j.md`, the uniform-completion/window source `M1196__round4_energy.md`, and the DC/MS source are included as inherited mathematical dependencies. The first OPICA paper is also included. Their status does not increase by being copied or cited.

A fresh GitHub main-reference read returned `97926d6a949fed7af0429a373b47abc772012834`. A fresh open-PR read returned an empty array. This is a visibility observation, not evidence that the parallel implementation workspace is idle. No whole-repository tree download, compiler execution, or final-head Post-Green harvest was performed in this round.

The original archive already has the first-drive estimate of the form $\exp(-c e^{t/2})$ (A03; later used by M0608), and already has fixed-order faster-than-every-exponential estimates for $R_{m,\ell}$. The extension here is the quantitatively uniform dependence on the left contour parameter for **fixed $m,\ell$**, and its use to shrink the balance slack to $O(\log T)$. It is not claimed that double-exponential decay first appeared in this project today.

Classical zeta reflection, gamma strip estimates and Euler--Maclaurin are identified in the source register. Co-Poisson/Sonine constructions and zero systems have substantial prior literature, notably Burnol; no general priority claim is made. The actual proofs of the stated new interfaces are written below.

# 1. Fixed source, notation and the inherited inputs

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

# 2. Q1--Q2: quantitative fixed-order forward localization

## 2.1 Lemma Q1a: a vertical estimate uniform in the real part

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

## 2.2 Lemma Q1b: moving left-line zeta cost

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

## 2.3 Theorem Q2: double-exponential forward decay

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

# 3. Q3: the exact native corridor needs only logarithmic slack

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

## 3.1 Theorem Q3

For all sufficiently large $T$, on the whole window $I_T$ there is an exact identity

$$F_m=E_T+\mathcal B_T,\tag{Q3.2}$$

where

$$
\mathcal B_T(t)=
\sum_{\substack{Y_T<n_1,\ldots,n_r\le Z_T\\(n_1\cdots n_r,Q_T)=1}}
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

## 3.2 A concrete fixed-source instance

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

## 3.3 High-mask transfer on this schedule

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

# 4. O1--O2: source-aware recovery with its complete cost

A contrast may lose the coherent observation but leave a source-history channel that recovers it. OPICA must check both information and cost.

## 4.1 Theorem O1: exact constrained recovery

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

## 4.2 Theorem O2: noisy recovery and rate budgets

If the measured vector $y$ satisfies $\|y-Ax\|\le\varepsilon$, then

$$\boxed{|\ell(x)-Ry|\le\kappa_A\varepsilon.}\tag{O2.1}$$

Thus a family of exact recovery maps can be used on a schedule only after pricing $\kappa_{A_n}$ and every observation/history error. For example, $\log(1+\kappa_{A_n})=o(T_n)$ and $\log(1+\varepsilon_n)=o(T_n)$ make the scalar recovery error subexponential. To transfer a positive target rate, one must also retain the target in the measured data; smallness of a contrast alone is still insufficient.

A sharp elementary control is $P=I-uu^*$ for a unit vector $u$, $Cx=\epsilon\langle u,x\rangle$, and $\ell(x)=\langle u,x\rangle$. Algebraic recovery exists for every $\epsilon\ne0$, but its optimum norm is $1/|\epsilon|$. Choosing $\epsilon=e^{-aT}$ incurs positive exponential cost. Injectivity at each finite stage is not a uniform observation theorem.

The compatibility test has an equally explicit error version. For $B:\mathbb C^d\to\mathbb C^N$, there exists $\alpha$ with $\|b-B\alpha\|\le\varepsilon$ exactly when $\operatorname{dist}(b,\operatorname{Ran}B)\le\varepsilon$. A unit left-annihilator $y$ with $|y^*b|>\varepsilon$ certifies incompatibility. This follows from finite-dimensional orthogonal projection. Counting rows does not construct that certificate.

# 5. J1: robust local jets, including changing completion depth

Let a corrected native transform at stage $n$ have coefficient $a_{j_n,n}\ne0$ at degree $j_n\ge-1$ in its Laurent expansion around $\lambda$. On a common circle $|z-\lambda|=r>0$, suppose an approximation has meromorphic error $e_n$ with no other interior pole and

$$\sup_{|z-\lambda|=r}|e_n(z)|\le E_n.$$

## Theorem J1

The error in that Laurent coefficient satisfies

$$\boxed{|\Delta a_{j_n,n}|\le r^{-j_n}E_n.}\tag{J1.1}$$

In particular, the observed coefficient cannot vanish if

$$E_n<|a_{j_n,n}|r^{j_n}.\tag{J1.2}$$

For repeated native completions, $j_n=p_nm-1$ and the true coefficient is the explicit NB1 coefficient, not its unnormalized derivative. Its amplitude, $r^{-j_n}$ and all affine corrections must be priced together.

**Proof.** The Laurent coefficient is the contour integral of $e_n(z)/(z-\lambda)^{j_n+1}$ divided by $2\pi i$. Its length estimate is exactly (J1.1). The reverse triangle inequality proves (J1.2). Equality is sharp: the perturbation $-a_{j_n,n}(z-\lambda)^{j_n}$ cancels the coefficient and has circle norm $|a_{j_n,n}|r^{j_n}$. $\square$

For $j=-1$ this is the residue bound $rE$. For nonnegative $j$, the derivative error is $j!r^{-j}E$. A proof that controls only compact time intervals, a distant convergence half-plane, or an unrelated norm does not supply this circle budget.

This gives a completed finite-to-infinite interface for the displayed local observations. It is not an assertion that the actual approximation errors satisfy it. Coupling this result with NB1 and O2 gives a concrete native preservation test: the true corrected coefficient survives whenever the full perturbation/recovery budget is strictly below its actual value. The condition is not replaced by the words “small error.”

# 6. Audit of the renormalized co-Poisson family

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

# 7. S1: the actual zero profile, its jumps, and the retained forcing

## 7.1 Theorem S1a: stronger tail and regularity

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

## 7.2 Theorem S1b: exact Euler equation

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

# 8. S2: an exact native multi-zero sampling compatibility law

For any finite set of actual zeros, choose one representative for each distinct $\kappa_i=\rho_i(1-\rho_i)$. Define

$$
N_{ij}=\int_0^\infty h_{\kappa_i}(x)\overline{h_{\kappa_j}(x)}dx,
\quad
Q_{ij}=\int_0^\infty x^2h_{\kappa_i}'(x)\overline{h_{\kappa_j}'(x)}dx,
$$

$$S_i=\sum_{n\ge1}h_{\kappa_i}(n),\qquad b_i=S_i-\tfrac12.$$

All integrals and sums converge absolutely in the required sense by S1. The inner-product convention in this section is linear in the first argument.

## Theorem S2

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

### A falsification of the automatic spectral-exclusion inference

Take any positive real diagonal matrix $A$, a nonzero real vector $g$, and nonreal parameters $\kappa_i$. Let

$$h_i=\kappa_i(A-\kappa_i I)^{-1}g,\qquad b_i=g^*h_i.$$

The same algebraic identities (S2.1)--(S2.3) hold with $N_{ij}=\langle h_i,h_j\rangle$ and $Q_{ij}=\langle Ah_i,h_j\rangle$. Nonreal parameters are entirely compatible with these positive Gram matrices because the equation is forced. This is an auxiliary finite-dimensional control, not a second genuine zeta system. It rejects only the inference from positivity and the displayed identities to reality of the parameters.

An additional source-sensitive fact about the actual $S_i$ might still matter. No such independent opposing fact is supplied here.

# 9. H1--H2: every finite multiplicity-sensitive co-Poisson combination is tested

## 9.1 Theorem H1: actual zero jets remain measures with the exact gap

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

## 9.2 Theorem H2a: finite independence, with reflection removed correctly

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

## 9.3 Theorem H2b: no nonzero real finite combination enters the positive cone

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

# 10. H3: an explicit correction cost in the first lattice interval

For the normalized real single-zero measure from Round 1, let $\lambda=\delta+i\gamma$, $|\delta|<1/2$ and $|\gamma|\ge16$. Put

$$u_1=\frac{4\pi}{3|\gamma|},\qquad u_2=\frac{5\pi}{3|\gamma|},\qquad J_\gamma=[e^{u_1},e^{u_2}].$$

## Theorem H3

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

# 11. S3: a nonlinear square repairs the sign but has a nonremovable duality defect

The preceding results exclude finite linear repairs within the zero-jet family. A different candidate is to square its gapped function, obtaining positivity directly.

Let $h\in L^1\cap L^2$ be an even continuous Fourier-self-dual function, vanishing at infinity, and suppose $h=A$ on $[-1,1]$ for a complex constant $A$. Put $f=A-h$, and define

$$\tau_h=|f(x)|^2dx-|A|^2\sum_{n\ne0}\delta_n.$$

For the actual zero profile use $h=h_\kappa$, $A=1$. Finite real or complex combinations of those profiles also fit with the appropriate $A$.

## Theorem S3

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

# 12. Integrated native architecture and its remaining independent input

The following now forms one closed **paper interface** for the displayed arithmetic branch:

$$
\begin{gathered}
\text{literal }j_m,\ \text{exact integer/Möbius identities}\\
\Downarrow\\
\text{Q1--Q2 quantitative forward localization}\\
\Downarrow\\
\text{Q3 fixed-order logarithmic-slack decomposition}\\
\Downarrow\\
\text{actual low-mask budget + norm-first comparison}\\
\Downarrow\\
\text{same high-mask observed rate as }F_m\\
\Downarrow\quad\text{using inherited J5.2}\\
\text{high-mask rate}=\Theta.
\end{gathered}
$$

Every arrow above has a written argument and named inputs. This does **not** append the assertion $\Theta=0$. No estimate in Q1--Q3 controls the complete signed high-mask form from above at a smaller rate. In particular, the new polynomial balance does not make the factors independent, remove the coherent rational character rows, or provide OPEN-J46.

The local branch now has NB1's named native generators, the affine correction ledger and J1's exact contour-error test. Its finite nonzero class survives whenever the actual relative error budget passes. It still cannot turn an arbitrary meromorphic continuation into a convergent physical integral.

The observation branch now allows source-history recovery, with its exact kernel condition and norm. This closes the algebraic question that a contrast may preserve information jointly with other channels, while retaining the possibility of exponential recovery cost.

The heat branch now contains:

1. the exact sharp-gap separator;
2. the compact and absolutely convergent noncompact mixer exclusions;
3. quantitative near-gap/variation control;
4. a legitimate actual-zero family and its arbitrary-multiplicity jets;
5. finite independence and cone separation;
6. explicit negative-mass cost;
7. an exact forced spectral/sampling identity; and
8. a nonlinear square test whose unrepaired Fourier defect is quantified.

This is a considerably more complete obstruction map. It is not an independent exclusion of a genuine off-line zero. The tested fields and measures are consistent constructions conditional on that zero, just as they are meaningful at critical-line zeros. The extra native law needed to contradict them has not been proved.

## 12.1 What is ready for a follow-up PR

Theorems in this document are mathematical specifications with proofs. Suggested implementation families, **not files already created in the repository**, are:

| Family | Paper target | Dependency that must not be assumed away |
|---|---|---|
| `NativeForwardLocalization` | Q1--Q2 | Actual box-product transform, uniform gamma/zeta estimates, inverse Laplace identification |
| `LogarithmicBalancedInverse` | Q3 | Genuine Dirichlet convolution identity, real cutoff/support bounds, palette shifts |
| `ObservationRecoveryCost` | O1--O2 | Real operator norm of the joint observation and all history errors |
| `RobustNativeJets` | J1 + NB1 | Exact correction ledger, Laurent coefficients, common contour domain |
| `CoPoissonZeroJets` | H1--H2 | Round 1 CP1 measure existence, parameter differentiation and multiplicities |
| `CoPoissonEulerProfile` | S1 | Functional equation, Euler--Maclaurin tail, jump terms and measure/function identity |
| `SamplingBoundaryForm` | S2 | Convergent sampling, piecewise integration by parts, no deleted lattice forcing |
| `CoPoissonSignControls` | H3, S3 | Actual profile, Fourier normalization, full off-lattice sign and lattice-correction class |

Exact module placement must be reconciled against the **finished** first PR. No new implementation is begun here, no existing claim is promoted, and no proposed theorem receives Lean authority from this table.

## 12.2 The explicit incomplete goals

The following are not completed by this paper:

* an independent complete signed arithmetic upper or OPEN-J46;
* source-specific completed-input range membership or a full original Schur upper;
* a native contact-generated nonzero measure in the entire forbidden sharp-gap cone;
* independent review and Lean formalization of these new analytic proofs;
* final-head Post-Green proof/axiom/workflow harvest for the parallel first PR;
* a global originality review of the co-Poisson or spectral statements.

The full OPICA programme includes some of these goals. Calling that programme complete would be inaccurate. The completed object delivered here is the explicit second paper theorem tranche and its scoped countertests.

# 13. Adversarial checks and proof obligations resolved

| Risk | Resolution in the paper |
|---|---|
| Optimize a fixed-strip bound without knowing its constants | Q1--Q2 price the left-line index uniformly before choosing it |
| Claim a new first-drive estimate already in A03 | Historical $\ell=0$ result is acknowledged; the higher-kernel quantitative extension is isolated |
| Change $m$ silently | Q1--Q3 fix $m,\ell,r,d$ before the horizon limit |
| Pay palette mass but omit palette delay | Q3 subtracts $i\log Q_T$ explicitly in every Type I argument |
| Treat subexponential transfer as a signed upper | The full high-mask rate remains $\Theta$, not zero |
| Drop common-gcd overlaps or repeated primes | The exact coefficient identity and primitive mask are unchanged |
| Use finite recovery without a cost | O1 gives the optimum norm; O2 propagates measurement errors |
| Delete source histories after a contrast | The joint observation is $(P,C)$; known affine histories remain in it |
| Confuse Taylor coefficients and derivatives | J1 explicitly records the factorial conversion |
| Claim coefficient continuity from compact-time convergence | A common contour estimate is required |
| Confuse positivity of a quadratic form with positivity of a function | No off-lattice positivity is assigned to $h_\kappa$ or its density |
| Treat a zero-generated measure as a literal-$j$ identity | The heat map is a separately identified native integer-comb construction |
| Differentiate a conditional zero equation beyond its multiplicity | H1 stops at the actual multiplicity minus one |
| Count reflected zeros as independent | H2 uses distinct $\kappa=\rho(1-\rho)$ and confluent Hermite jets |
| Infer a uniform frame constant from finite independence | H2.2 is explicitly fixed-system only |
| Apply a homogeneous self-adjoint argument to $h_\kappa$ | S1 retains the nonzero lattice-minus-continuum force and identifies the operator-domain failure |
| Use divided-difference denominators at conjugate-coincident nodes | S2.2 is the undivided identity; division is conditional |
| Claim all zero heights meet the sign-test cutoff | H3 retains $|\gamma|\ge16$ as an explicit hypothesis |
| Square a field and assume Fourier self-duality | S3 computes its nonzero duality defect and excludes lattice-only repair; the exact self-dual projection fills the gap |
| Call finite/numerical checks analytic proof | Execution receipts have separate authority labels |

The new proofs were checked by the authoring model against boundary cases and alternative algebraic representations. This is a self-audit. It is not represented as independent peer review.

# 14. Validation and research-state harvest

The evidence packet contains two classes of controls. The exact checker uses rational/symbolic algebra and checks the finite identities, Hermite ranks, exponent bookkeeping, recovery examples, sampling-form controls and Euler-cell/jump identities. It does not evaluate a hypothetical off-line zeta zero or prove an infinite bound. The numerical checker compares finite-cutoff analytic representations and the Euler--Maclaurin remainder at ordinary nonzero arguments; those checks are not interval certified.

The new checker passed **14,672 exact finite assertions in each of normal and optimized Python**. Their group counts and checker hashes agree. The separate numerical checker passed **15 consistency cases**: three finite-window Green identities with the exterior boundary retained, three finite-sum Euler--Maclaurin comparisons, and nine first-interval sign fixtures. These cases use ordinary nonzero arguments or explicitly synthetic parameters, not hypothetical off-line zeros. Numerical checks are not interval certified.

The original Round 1 checker was replayed unchanged in both normal and optimized Python. Each run passed its original 18,862 finite checks, with unchanged group counts and checker hash. This preserves earlier finite evidence, not new theorem authority.

Exact new check counts, hashes and numerical case dispositions are recorded in the final receipts; they are generated from executed code rather than hard-coded into this manuscript. The release manifest binds those receipts, this paper and its theorem ledger. PDF rendering is presentation QA, not mathematical review.

**What became formally true:** no new Lean theorem. The new statements have written proofs at PAPER/DERIVED authority. Existing pinned source proofs were not recompiled.

**Workflow harvest:** no GitHub job was started; no first-PR result was presumed green. The only live operational facts used are the main ref and the visible open-PR read. Local exact and numerical runs are classified separately.

**What changed:** arithmetic balance can now be logarithmically slack at fixed source order. The local/observation error budgets are explicit. Finite multi-zero/jet heat repairs and the squared-density repair are fully tested for the displayed families. The actual spectral equation exposes its retained force and sampling term.

**Upstream implications:** source regularity can be used quantitatively rather than hidden in per-strip constants. The sharper budget removes the need for a moving source in this arithmetic preparation. Finite observation recovery has to retain history and its condition number.

**Downstream implications:** a signed estimate can target the precise polynomial-width factor region. A contact or spectral argument must control the actual sampling/forcing term rather than infer an eigenvalue equation from local homogeneous cells.

**Resurrected routes:** fixed low-order arithmetic becomes cleaner. Multi-zero co-Poisson **linear** sign repair is excluded on each finite generated span, not all multi-zero arguments. Nonlinear maps are not ruled out generally; the obvious square is ruled out explicitly.

**New RH-relevant clue:** the self-dual profile has a positive real differential quadratic form but a source-dependent complex sampling defect. Any genuine spectral exclusion must account for that exact defect. The completed identities do not force it to vanish.

**Fastest remaining independent test:** obtain a signed gain for the complete tightly balanced native interaction, or a new theorem for the source-specific sampling term that is not already an identity of the forced system. Neither is supplied in this tranche.

**Claim state: Step 4 OPEN; RH OPEN.** No result above is advertised as an improved zero-free region or proof that such a region cannot be obtained.

# 15. Sources and reproducibility

## Project sources

**P0.** `OPICA_Paper_Construction_v1_0_2026-10-21.md`, especially local laws L1--L5, arithmetic A1--A3, observation O1--O4, and signed separator H1. Its original paper status is retained.

**P1.** `OPICA_Beyond_PR_Research_Round1_2026-10-21.md`: NB1, AT1--AT2, HT1--HT2, CT1, MC1, CP1. Its full source and executed checker are included. [Verified Drive source](https://drive.google.com/file/d/1M_EmuJczExFmIA5IN51sOCN8xaF0rUl6/view).

**P2.** Original M0659, `continuation_native_j.md`, 18 October 2026: actual one-$Q$ source, fixed-order rapid forward kernels, J17 decomposition, J5.2, and the genuinely open signed estimate. Physical handover navigation approximately 8768--8781. Preserved source body included.

**P3.** Original M1196, `round4_energy.md`: auxiliary completion and logarithmic-window proof. Preserved source body included; not formalized anew.

**P4.** *Divisor-Controlled Mask Transfer and Moving-Source Continuation*, 20 October 2026: DC1/DC2 and MS1. The preserved export is included. [Source document](https://docs.google.com/document/d/1KcUovuIEsqhmJ25Yqn3U-ItDmLVEVRJx-_Ltpp_CYTA/edit).

**P5.** A03 first-drive Poisson localization and M0608's later source-correct use, as retrieved from `RH_Step4_Third_Party_Complete_Handover.pdf`. The first-drive double-exponential scale is inherited, not claimed new.

**P6.** Fresh main reference and visible open-PR list, `HMarcusWH/zeta-23-lean`, 21 October 2026. Observed main `97926d6a949fed7af0429a373b47abc772012834`. No new tree/CI certification.

## External primary formula sources and context

**E1.** NIST DLMF 25.4.2, zeta reflection formula: <https://dlmf.nist.gov/25.4.E2>. Used in Q1b. Formula recalled with proof-domain assumptions in the text, not a new native zero-free theorem.

**E2.** NIST DLMF 5.11, gamma asymptotics and uniform strip estimates: <https://dlmf.nist.gov/5.11>. Used with the exact recurrence to price the moving left line. Only a fixed base gamma strip needs the classical asymptotic bound.

**E3.** NIST DLMF 25.11(iii), finite sums/Hurwitz Euler--Maclaurin representations: <https://dlmf.nist.gov/25.11>. Used for the explicitly derived expansion S1.3 and its locally uniform parameter version.

**E4.** Jean-François Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta function*, JTNB 16 (2004), 65--94, DOI 10.5802/jtnb.434. [Primary publication](https://numdam.org/articles/10.5802/jtnb.434/). Relevant context for co-Poisson/Sonine/zero systems; no general novelty claim and no theorem silently imported as a native closing estimate.

The main derivations are written in this document. The copied inputs, exact checker and receipts are hashed in the package. Temporary authenticated download links are excluded. The normal and optimized exact-check commands and numerical command are in `README.md`.
