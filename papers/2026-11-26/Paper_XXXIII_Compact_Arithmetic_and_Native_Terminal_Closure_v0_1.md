# Compact arithmetic supply and native terminal closure

**Paper XXXIII — Weil–CCM/OPICA programme**  
Marcus Hermansson · 26 November 2026 · Version 0.1, review candidate

**Abstract.** We replace the large original arithmetic supplier of Paper XXXII with the compressed Alpöge/Claude/Anthropic arithmetic development. A fixed-modulus weighted prime-remainder theorem supplies a principal-character zero-strip estimate at each specified tolerance. We expose the arithmetic cancellation, exact Mellin centering and multiplicity-sensitive twist selection. Two terminal compositions follow: the direct physical-slice composition implemented in PR #319, and a literal prime-ramp energy composition retaining the power comparison of Papers XXX–XXXI. The former derives critical-line confinement before using C1; the latter needs only a single arithmetic tolerance after the comparison margin has been fixed. Neither imports an upstream terminal RH/GRH declaration. Both rely on attributed arithmetic and analytic results, and neither constitutes an independent derivation of that arithmetic. The common-pin kernel and independent replay gates remain open at the recorded inspection.

## 1. Scope and earlier results

Let $Z$ be the distinct actual nontrivial zeros of $\zeta$, counted with their positive integer multiplicities $m_\rho$ in sums. We use the ordinary critical strip and functional-equation reflection. Define the nonattainment-safe displacement

$$
a=\sup(\{0\}\cup\{|\Re\rho-1/2|:\rho\in Z\}).
$$

Thus $0\le a\le1/2$. We do not suppose that a rightmost zero exists.

Paper XXVIII fixes the canonical finite Weil form, its physical moment slices, and the cofinal consumer C1. Paper XXX supplies the eventual positive-energy obstruction and an integrated explicit formula; Paper XXXI supplies the both-parity power comparison. Paper XXXII describes the older principal host/TopG route of PR #317. Papers XXIV and XXIX study separate signed arithmetic observables. Their finite identities are neither substituted for the literal ramp nor claimed to establish their independent upper/lower targets. The present paper changes the arithmetic supply, not the detector.

The nonstandard inputs used below are: the compact source's admissible-data, short-form, spanning, long-form, second-scale and twist-avoidance theorems; the native exact Weil dictionary and both-parity fixed-margin witnesses; and, for the energy route, the integrated explicit formula and the native power comparison. All are identified in Section 7. Their complete underlying geometric and detector proofs are not reproduced here.

## 2. The attributed weighted arithmetic upper

Fix $M=18480$ and $c_0=9239=M/2-1$. Let $\mathcal D$ be the primes $d\equiv c_0\pmod M$. Since $M=2(c_0+1)$ and $c_0$ is odd, $\gcd(c_0,M)=1$; moreover $c_0\equiv7\pmod8$. For every such prime $d$, $M\mid2(d+1)$ but $M\nmid d+1$. Dirichlet's theorem makes the class nonempty. Put $\chi_d(n)=(n/d)$ and

$$
\lambda_{d,M}(n)=\Lambda(n)\mathbf1_{n\equiv1\ (M)}(1-\chi_d(n)),
$$

$$
R_{d,M}(x)=\sum_{n\le x}\lambda_{d,M}(n)(1/n-1/x)
-\frac{\log x}{\varphi(M)}-c_{d,M}.
$$

Here $c_{d,M}$ is the exact constant in Section 3. All prime powers, including any ramified contributions, retain their original weights. The sum is continuous at each integer hinge.

**Theorem 2.1 (attributed arithmetic input).** For fixed $d\in\mathcal D$ and $0<\varepsilon<1/100$, eventually for real $x$,

$$R_{d,M}(x)\le x^{-1/2+8\varepsilon}.$$

This is the compact declaration eventually_primeError_le_rpow, retained in the arithmetic-only source cut. The following is its scalar assembly, not a replacement for the deep proofs of its inputs.

For admissible data write $D>0$ for the row dimension, $n$ for the number of selected independent rows, $m$ for the number of lifts, $A$ for the long order, $f$ for the infinite-place count, and $b$ for the auxiliary size. Set $B=fA(\log b)^3$, $J=B\log b$, $H$ for the common main height, $r$ for the exact total remainder, and $I$ for the logarithmic index allowance. The short/enough/long theorems applied to the same family give, with $h=H-mr+J$,

$$
D(H-3J)\le nh+2I,\qquad
0\le D-n\le4D/b^2,
$$

$$I\le5D\log(1+b^2)B,\qquad -h\le b^2x^{99}.$$

Substitute $nh=Dh+(D-n)(-h)$ and divide by positive $D$. The common height cancels:

$$mr\le4J+4x^{99}+10\log(1+b^2)B
\le B(\log b)^2.$$

The final inequality is the source's admissible-size bound; its hypotheses are part of the data, not a general inequality for arbitrary parameters. With $T$ and $U>0$ the top and thick place counts, the same remainder satisfies

$$
R_{d,M}(x)=\frac{r}{AU}
+R_{d,M}(x_1)-\frac{T}{U}R_{d,1}(x_1).
$$

The data theorem and second-scale lemma provide, for every sufficiently late $x$, the admissible updated datum with $f=\varphi(M)T$, $m\ge\sqrt x$, $T/U\le\log b$, $\log b=x^\varepsilon$, and the last two terms together at most $x^{-10^6}$. Specifically the source uses its signed-window lemma on $\log x_1\in[t,t^2]$ with $t=10^6\log x$, modifies that field of the original datum, and re-establishes the scale conditions; it does not combine unrelated families. Hence

$$
R_{d,M}(x)\le\varphi(M)x^{-1/2+6\varepsilon}
+x^{-10^6}\le x^{-1/2+8\varepsilon}
$$

eventually. The constants and lateness threshold may depend on the fixed parameters.

Define the fixed-tolerance premise $\mathcal U(\beta)$, for $1/2<\beta<1$, to be the assertion that for every $d\in\mathcal D$ there exists $X_{d,\beta}$ such that $R_{d,M}(x)\le x^{\beta-1}$ for all $x\ge X_{d,\beta}$. Theorem 2.1 supplies $\mathcal U(\beta)$: choose $\varepsilon=(\beta-1/2)/51$. Then $0<\varepsilon/6$, $\varepsilon<1/100$, and $-1/2+8\varepsilon\le\beta-1$. This is exactly the parameter selection of NativePrincipal.lean. No threshold uniform in $d$ is required.

## 3. Exact Mellin interface and fixed-tolerance exclusion

Let $\widetilde L_\psi(s)$ be the Dirichlet $L$-function, with its pole removed by multiplication by $s-1$ for the principal character and analytic continuation at 1. Twisted characters $\psi\chi_d$ are modulo $Md$ and are nonprincipal: CRT gives a unit equal to 1 modulo $M$ and a nonresidue modulo $d$. Write $m_\psi(\rho)$ for the order of $\widetilde L_\psi$ at $\rho$. Set

$$
A_d(s)=\frac1{\varphi(M)}
\left[\sum_{\psi\bmod M}
\left(\frac{\widetilde L'_{\psi\chi_d}}{\widetilde L_{\psi\chi_d}}(s)
-\frac{\widetilde L'_\psi}{\widetilde L_\psi}(s)\right)-1\right],
\qquad c_{d,M}=\Re A_d(1).
$$

The character population is conjugation-invariant, so $A_d$ is real on the real axis wherever finite. Standard Dirichlet nonvanishing on $\Re s\ge1$ makes $c_{d,M}=A_d(1)$ well defined.

**Lemma 3.1 (exact transform).** For $\Re s>1$ the integral
$F_d(s)=\int_1^\infty R_{d,M}(x)x^{-s}\,dx$ is absolutely convergent and has continuation to $\Re s>0$ given by

$$F_d(s)=\frac{A_d(s)/s-c_{d,M}}{s-1}.$$

It is holomorphic on $\Re s\ge1$, and for $0<\Re\rho<1$ the possible simple-pole residue is

$$
\operatorname{Res}_{s=\rho}F_d(s)=
\frac{\sum_{\psi\bmod M}
(m_\psi(\rho)-m_{\psi\chi_d}(\rho))}
{\varphi(M)\rho(1-\rho)}. \tag{1}
$$

*Proof.* For $\Re s>1$,

$$\int_n^\infty(1/n-1/x)x^{-s}\,dx=\frac{n^{-s}}{s(s-1)}.$$

The inequality $0\le\lambda_{d,M}(n)\le2\Lambda(n)$ justifies the interchange of sum and integral. Orthogonality and Euler products give $\sum_n\lambda_{d,M}(n)n^{-s}=A_d(s)+s/(\varphi(M)(s-1))$. The logarithmic correction cancels the resulting double pole, and the constant term gives the displayed transform. Its numerator vanishes at 1. The logarithmic derivative at a zero of multiplicity $k$ has principal part $k/(s-\rho)$. This proves (1), including its sign. Conjugation gives $F_d(\bar s)=\overline{F_d(s)}$.

**Lemma 3.2 (one-sided moment criterion, paper derivation).** Suppose a real measurable locally bounded function $g(v)$ on $v\ge0$ satisfies $|g(v)|\le C_0e^{cv}$ and $g(v)\le C_1e^{\beta v}$, where $C_0,C_1>0$. Its Laplace transform $F$ continues meromorphically to $\Re s>\beta$ with only simple poles, is conjugation-symmetric, and every real pole in that half-plane has positive residue. Then it has no pole there.

*Proof.* If $p_0$ is such a pole, then for large real $\sigma>\max(c,\beta)$,

$$|\sigma-p_0|<\sigma-\beta$$

by expanding the squares. Avoid the countable set of distance ties between distinct nonconjugate poles. The closed disk of radius $|\sigma-p_0|$ is compactly contained in the half-plane, so there is a nearest pole distance $r<\sigma-\beta$ and the nearest set is either one real pole or one conjugate pair. Choose $r'$ strictly between $r$ and $\sigma-\beta$, with no other poles in the closed disk of radius $r'$. Differentiation of the absolutely convergent transform gives

$$
T_k=[z^k]F(\sigma-z)=\frac1{k!}\int_0^\infty
g(v)e^{-\sigma v}v^k\,dv
\le\frac{C_1}{(\sigma-\beta)^{k+1}}.
$$

After subtracting the nearest principal parts, Cauchy's estimate makes the remaining coefficient $O((r')^{-k})$. A real nearest pole has residue $P>0$, yielding $T_k=Pr^{-k-1}+O((r')^{-k})$. For a conjugate pair, write the residue $P=|P|e^{i\omega}$ and $\sigma-p=re^{i\phi}$. The coefficient is

$$2|P|r^{-k-1}\cos(\omega-(k+1)\phi)+O((r')^{-k}).$$

The angle $\phi$ is not a multiple of $\pi$. The averages of the cosines and their squares tend to 0 and $1/2$ by geometric summation. Infinitely many cosine values exceed $1/4$: otherwise $u^2\le1/4-3u/4$ eventually for these values $u\in[-1,1/4]$, contradicting the averages. Thus in either case $T_k\ge C_2r^{-k-1}$ for arbitrarily large $k$, with $C_2>0$. This contradicts the upper bound because $r<\sigma-\beta$.

**Theorem 3.3 (fixed principal strip).** If $\mathcal U(\beta)$ holds, and the attributed finite-height twist-avoidance theorem holds, every $\rho\in Z$ satisfies $\Re\rho\le\beta$.

*Proof.* Suppose $\Re\rho>\beta$. The compact theorem exists_entireL_quadTwist_ne_zero supplies one $d\in\mathcal D$ such that every $\widetilde L_{\psi\chi_d}$ is nonzero on $\Re s\ge\beta$, $|\Im s|\le|\Im\rho|$. This is finite-height avoidance, not a theorem excluding zeros of $\zeta$. At $\rho$ the negative multiplicities in (1) vanish. The untwisted principal character satisfies

$$L(s,\psi_0)=\zeta(s)\prod_{p\mid M}(1-p^{-s}).$$

The finite Euler factors and the pole-removing factor are nonzero at $\rho$. Its order is exactly $m_\rho>0$, and other untwisted orders are nonnegative. Therefore $\rho$ is a genuine pole of $F_d$. Every real pole with $\Re s>\beta$ must lie in $(\beta,1)$; the twist selection also covers that interval, so each such residue is positive by (1). Put $g(v)=e^vR_{d,M}(e^v)$. Continuity and $\lambda(n)\le2n$ give $|g(v)|=O(e^{2v})$. The fixed-$d$ arithmetic bound gives $g(v)\le e^{\beta v}$ eventually, hence $g(v)\le C_1e^{\beta v}$ globally after increasing $C_1$. Its Laplace transform is exactly $F_d$. Lemma 3.2 contradicts the pole. This proof does not assume simplicity of the zeta zeros.

PR #319 instead directly applies the inherited conditional entireL_ne_zero_of_primeError_le with the exact premise $\mathcal U(\beta)$. It uses the same principal Euler-factor identity. Lemma 3.2 is the independent paper exposition of the conditional pole argument, not a claim about the newly compiled declarations.

## 4. Original physical slices and C1

For $L>0$ take $K=\lceil L^4\rceil$, physical coefficients $u_n$ on $-K,\ldots,K$, moments $M_j(u)=\sum_n n^ju_n$ with $n^0=1$, reversal $(Ju)_n=u_{-n}$, and squared norm $\|u\|^2=\sum_n|u_n|^2$. The boundary-flat carrier has $M_0=M_1=M_2=0$. Its two pole profiles are

$$p_+(u)=\sum_n\frac{Lu_n}{L^2+16\pi^2n^2},
\qquad p_-(u)=\sum_n\frac{4\pi n u_n}{L^2+16\pi^2n^2}.$$

The even slice imposes $Ju=u$, $p_+=0$, $M_4=0$; the odd imposes $Ju=-u$, $p_-=0$, $M_3=M_5=0$. Both retain boundary flatness. On these carriers the canonical physical form $Q_p$ is exactly the real Weil self-form of the zero-extended normalized Fourier polynomial $f(t)=L^{-1/2}\sum_n u_ne^{2\pi int/L}$ on $[0,L]$, by the inherited dictionary of Paper XXVIII. In particular with $\gamma_\rho=-i(\rho-1/2)$ and $\widehat f(z)=\int f(t)e^{izt}\,dt$ its summands are $m_\rho\widehat f(\gamma_\rho)\overline{\widehat f(\bar\gamma_\rho)}$. The norm and canonical scalar correction are not adjustable.

Write $B_p(L;t)$ for the all-vector inequality $Q_p(u)\ge-t\|u\|^2$ on the exact slice. This is monotone in $t$. The inherited fixed-margin theorem says that an off-critical zero supplies $b_0>0,L_0$ such that at every $L\ge\max(2,L_0)$ both slices have a nonzero vector with $Q_p(u)<-b_0\|u\|^2$. Therefore

$$
\mathrm{C1}:\quad\forall n\in\mathbb N,\ n\ge1,\ 
\exists L\ge n+2:\ B_e(L;1/n)\lor B_o(L;1/n)
$$

implies RH: choose $n>\max(1/b_0,L_0,1)$, then the selected aperture meets the common obstruction tail and either entire-slice bound contradicts its own witness. The disjunction is outside both all-vector quantifiers. These are Paper XXVIII, Theorem 6.3, and CofinalMomentClosure.lean.

## 5. The direct closure in PR #319

Apply Theorem 3.3 at $\beta=(\Re\rho+1/2)/2$ for any hypothetical $\Re\rho>1/2$. It gives the contradiction $\Re\rho\le\beta<\Re\rho$. Reflection puts every actual nontrivial zero on the line. Now $\gamma_\rho$ is real, each Weil summand is $m_\rho|\widehat f(\gamma_\rho)|^2\ge0$, and the exact dictionary gives

$$B_e(L;0)\land B_o(L;0)\qquad(L>0).$$

For every $n\ge1$ take $L=n+2$. Monotonicity supplies C1, and the unchanged native consumer gives the stock nontrivial-zero statement of RH. This is the precise direct-slice terminal composition in PR #319. The confinement step is already RH-equivalent by reflection. Thus the subsequent C1 implication demonstrates compatibility of the original receiving interface with the supplied arithmetic, not a logically independent proof of the zero-free statement.

## 6. Single-tolerance closure through the literal energy

The alternative route retains the original observable, not the weighted remainder:

$$G(x)=\sum_{n\le x}\Lambda(n)(x/n-1)-x\log x+(1+\gamma_E)x,$$

$$E(Y)=\int_Y^{Y^{3/2}}[G(x)]_+^2\,\frac{dx}{x^2}\qquad(Y\ge2).$$

Paper XXX, Theorem 11.3, gives for $x\ge2$ the absolutely convergent formula

$$G(x)=-\sum_{\rho\in Z}\frac{m_\rho x^\rho}{\rho(\rho-1)}
+\log(2\pi)+\frac{x}{2}\int_x^\infty\frac{\log(1-u^{-2})}{u^2}\,du.$$

Its second denominator is paid by integration of the classical truncated explicit formula; the possible linear term is eliminated by the removable Mellin singularity at 1. The sum of the absolute coefficients converges by the classical zero count. Theorem 3.3 at just one fixed $\beta=1/2+t$, $0<t<1/2$, therefore gives $|G(x)|\le K_0x^{1/2+t}$ with the finite constant $K_0=\sum_\rho m_\rho/|\rho(\rho-1)|+|\log(2\pi)|+1$. Here the elementary integral has absolute value at most $2/(9x^2)$ for $x\ge2$. Consequently

$$E(Y)\le\frac{K_0^2}{2t}(Y^{3t}-Y^{2t}). \tag{2}$$

Paper XXXI, Theorem 5.3, supplies one fixed $\delta>0$ and one eventual common tail on which

$$B_e(\log Y;E(Y)Y^{-\delta})\land
B_o(\log Y;E(Y)Y^{-\delta}). \tag{3}$$

For completeness, its positive-displacement case uses the strip floor $C_pY^{5a/4}$ and the eventual energy lower $E(Y)\ge Y^{2a}$ of Paper XXX. Absorb $\max_p C_p$ into $Y^{a/4}$ and take $\delta=a/2$. The case $a=0$ uses conditional critical-line positivity, with $\delta=1$. Neither case assumes an arithmetic upper. This is a supplier-free comparison relative to the prior analytic and spectral results, not a new estimate of $E$.

Fix $\delta$ from (3) first and choose $t=\min(\delta/12,1/8)>0$. Only $\mathcal U(1/2+t)$ is now needed from the arithmetic theorem. Equation (2) gives $E(Y)Y^{-\delta}\le C Y^{-3\delta/4}$ with $C=K_0^2/(2t)$. For any positive integer $n$ choose $Y$ beyond the comparison tail and at least $\max(2,e^{n+2},(Cn)^{4/(3\delta)})$. At $L=\log Y$ both $B_e(L;1/n)$ and $B_o(L;1/n)$ hold by monotonicity. C1 follows and the fixed-margin contradiction of Section 4 concludes RH. Alternatively, using arbitrary positive $t$ in (2) gives the stronger all-late subpower supply $E(Y)\le Y^\eta$ for each $\eta>0$ by choosing $t\le\eta/6$ and absorbing the constant.

The two routes share the same attributed arithmetic. The energy route does not invoke all-tolerance confinement as an RH theorem, but its fixed-tolerance transport still uses one-sided pole exclusion. It is not a Landau-free or independent arithmetic proof. Its distinct content is the exact transfer into the native positive energy and simultaneous physical bounds. It has not been formalized as part of #319.

## 7. Exact source and review boundary

The arithmetic is credited to Levent Alpöge with Claude and Anthropic. The compact upstream is Apache-2.0 licensed (copyright 2026 Anthropic, PBC); see [pinned source, attribution, and license](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207). The materialized source-port head is [b1e3e3e99fd913ba2b3560ceb3b5436cdb71f736](https://github.com/HMarcusWH/zeta-23-lean/tree/b1e3e3e99fd913ba2b3560ceb3b5436cdb71f736), on native base #316. Source locations at that head:

- [ArithmeticOnly.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/b1e3e3e99fd913ba2b3560ceb3b5436cdb71f736/Zeta23Arithmetic/New/ArithmeticOnly.lean): star_inequality, eventually_primeError_le_rpow. Its inputs include New/Endgame/ShortAndEnough, New/Endgame/LongForms, New/Data/DataExist, and New/Endgame/OneSidedCriterion.
- [NativePrincipal.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/b1e3e3e99fd913ba2b3560ceb3b5436cdb71f736/Zeta23Arithmetic/NativePrincipal.lean): principal_weighted_upper and principal_fixed_strip. The Mellin and twist inputs are in the relocated New/Endgame/PrimeError, New/Endgame/OneSidedCriterion and Lib/Analytic/QuadraticTwist/ZeroFreeTwist.
- [Terminal.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/b1e3e3e99fd913ba2b3560ceb3b5436cdb71f736/Zeta23/OPICANativeTerminal/Terminal.lean): actual_zero_re_le_half, actual_critical_line_arithmetic, both_parity_zero_floor_arithmetic, step4C1_native_arithmetic and riemannHypothesis_step4_native_arithmetic.
- Native MomentSlices, ZeroFreeFloor and CofinalMomentClosure (under Zeta23/OPICARound4/ArithmeticFrontier) preserve the original carrier, zero floor and C1 consumer. The separate energy comparison is documented by Papers XXX–XXXI and the conditional roots in [PR #317](https://github.com/HMarcusWH/zeta-23-lean/pull/317).

The source acquisition retains 792 arithmetic-only local modules, including the cut root, with 791 original proof bodies reversibly relocated and one frozen arithmetic cut. It excludes the public endpoint modules. The common native epoch pins Lean 4.35.0 and Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. See [PR #319](https://github.com/HMarcusWH/zeta-23-lean/pull/319) and [run 45716397974](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/45716397974). At inspection, materialization and source commit passed, common-pin compilation was running, and independent replay had not been observed. Source authentication and endpoint omission are not proof-value closure or kernel validation. Required later checks include exact stock theorem type, complete dependency and standard-axiom audits, fresh independent replay, specialist review and canonical acceptance. The historic archive retains its original scientific status.

**Conclusion.** The exact terminal implications are derived relative to the named arithmetic and native inputs. The paper identifies the closing interface and its two compositions, not a new self-contained proof of all inherited geometry, cohomology, and detector construction. No unconditional proof acceptance or independently supplied native signed arithmetic bound is announced.
