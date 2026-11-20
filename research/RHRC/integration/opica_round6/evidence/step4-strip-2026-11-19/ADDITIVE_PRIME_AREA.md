# A finite negative bound for the ordinary-prime area

**DERIVED on paper with interval-checked constants.** For \(\vartheta(u)=\sum_{p\le u}\log p\) and \(A_\vartheta(x)=\int_2^x(\vartheta(u)-u)\,du\),
\[
 A_\vartheta(x)=\sum_{p\le x}(x-p)\log p-\frac{x^2-4}{2}
 <-0.17x^{3/2}\qquad(10^{19}\le x\le10^{46}).                 \tag{1}
\]
The inequality holds for every real \(x\) in the stated range. The published pointwise sign \(\vartheta(u)<u\) on \([2,10^{19}]\) gives \(A_\vartheta(x)<0\) for the remaining \(2<x\le10^{19}\). The proof below only uses a finite verified zero height. [Büthe, Theorem 2](https://arxiv.org/pdf/1511.02032) · [Johnston, Lemma 2.1](https://arxiv.org/pdf/2201.06184#page=3)

## Inputs to the explicit formula

Write \(R_1(y)=\int_2^y(\psi(u)-u)\,du\). Subtract the integrated explicit formula at \(y=2\) from its value at \(y\). For \(y\ge2\) this gives
\[
 R_1(y)=-\sum_\rho\frac{y^{1+\rho}}{\rho(\rho+1)}
        -(y-2)\log(2\pi)+b(y),
\]
\[
 b(y)=\sum_\rho\frac{2^{1+\rho}}{\rho(\rho+1)}
 +\sum_{j\ge1}\frac{2^{1-2j}-y^{1-2j}}{2j(2j-1)} .
\]
The sums include both signs of the ordinates and all multiplicities. The trivial-zero term is between zero and one. The full reciprocal-ordinate sum is \(<s_0=0.04621\), and \(|\rho(\rho+1)|\ge|\Im\rho|^2\). Thus \(|b(y)|\le b_0=4s_0+1\). Subtraction avoids any numerical use of the additive zeta-derivative constant. [Johnston, proof of Lemma 2.6](https://arxiv.org/pdf/2201.06184#page=4) · [Brent, Platt and Trudgian, Corollary 1](https://arxiv.org/pdf/2009.13791#page=9)

Every nontrivial zero with \(0<|\gamma|\le H=3\cdot10^{12}\) lies on the critical line. The higher zeros obey the unconditional tail bound
\[
 S_H=\sum_{|\gamma|>H}\gamma^{-2}
 \ \le\ 2\left[\frac{1+\log(H/(2\pi))}{2\pi H}
       +\frac{0.14+0.56\log H}{H^2}\right]<4\cdot10^{-12}.
\]
This is the estimate for \(t^{-2}\) in the proof of Brent–Platt–Trudgian's Corollary 1 with the main integral evaluated. Their possible half weight at \(H\) only enlarges the bound on the strict tail. [Platt and Trudgian, Theorem 1](https://arxiv.org/abs/2004.09765) · [Brent, Platt and Trudgian, page 9](https://arxiv.org/pdf/2009.13791#page=9)

For \(t\ge121\), Johnston gives \(\psi(t)-\vartheta(t)>0.98\sqrt t\). For \(2\le t<121\) the difference is nonnegative. Consequently
\[
 A_\vartheta(y)\le R_1(y)-\frac{49}{75}(y^{3/2}-1331)
 \qquad (y\ge121).
\]
This uses the actual proper-prime-power contribution to \(\psi\) with its positive sign. [Johnston, Lemma 2.3](https://arxiv.org/pdf/2201.06184#page=3)

## Additive averaging on the full real interval

Fix \(10^{19}\le x\le10^{46}\). Set \(r=64,\ a=x^{3/4}/5\), and let \(U\) be the sum of \(r\) independent uniform variables on \([-a,a]\). Its law is just a compactly supported positive integration kernel. We have
\[
 \mathbb E U=0,\qquad \operatorname{Var}U=\frac{64}{75}x^{3/2}.
\]
For either \(Y=x+U\) or \(Y=x+2U\) we have \(121<Y\le(1+\delta)x\), with \(\delta=(128/5)(10^{19})^{-1/4}<0.001\). The same number bounds the relative displacement below \(x\).

For a zero above \(H\), integrate \(y^{1+\rho}\) successively against the \(r\) uniform densities of half-width \(a'\), where \(a'\) is either \(a\) or \(2a\). The exact expression is the signed sum of the \(2^r\) endpoints raised to \(1+\rho+r\), divided by \((2a')^r\prod_{j=2}^{r+1}(\rho+j)\). All endpoints lie in the displayed positive interval. Their complex powers use the real natural logarithm. Therefore
\[
 \left|\frac{\mathbb E Y^{1+\rho}}{\rho(\rho+1)}\right|
 \le \frac{((1+\delta)x)^{r+2}}{a^r|\gamma|^{r+2}}.
\]
This uses only \(0<\Re\rho<1\). Absolute convergence on this compact window, already implied by \(\sum\gamma^{-2}<\infty\), permits the exchange with the full zero sum. The aggregate high-zero cost divided by \(x^{3/2}\) is at most
\[
 W=(1+\delta)^{66}\,10^{23}
     \left(\frac{5(10^{46})^{1/4}}{H}\right)^{64} S_H
 <0.001.                                                       \tag{2}
\]
Each verified low zero contributes at most \(\mathbb E Y^{3/2}/|\gamma|^2\). Thus its whole contribution is at most \(s_0\mathbb E Y^{3/2}\).

The function \(A_\vartheta(x)+x^2/2\) is convex, since its derivative is the nondecreasing ordinary-prime counting sum \(\vartheta(x)\) away from its jumps. Jensen's inequality gives
\[
 A_\vartheta(x)\le\mathbb E A_\vartheta(x+U)+\tfrac12\operatorname{Var}U .
\]
Apply the proper-power lower bound inside the expectation. The linear term \(-(Y-2)\log(2\pi)\) is nonpositive. Since \(s_0-49/75<0\) and \(\mathbb E Y^{3/2}\ge x^{3/2}\), we obtain
\[
 \frac{A_\vartheta(x)}{x^{3/2}}
 \le s_0-\frac{49}{75}+W+\frac{64}{150}
       +\frac{b_0+(49/75)\,1331}{(10^{19})^{3/2}}.
\]
Using the actual upper enclosure in (2) gives a right side below \(-0.18045\), proving (1).

## Both signs of the integrated von Mangoldt error

For either averaging width the same calculation, now taking the absolute value of the linear term, gives
\[
 \frac{|\mathbb E R_1(Y)|}{x^{3/2}}
 \le W+s_0(1+\delta)^{3/2}
   +\frac{b_0/(10^{19})+(1+\delta)\log(2\pi)}{\sqrt{10^{19}}}
 <0.048 .
\]
The convex function \(R_1(x)+x^2/2\) gives both
\[
 R_1(x)\le\mathbb E R_1(x+U)+\tfrac12\operatorname{Var}U,\qquad
 R_1(x)\ge 2\mathbb E R_1(x+U)-\mathbb E R_1(x+2U)-\operatorname{Var}U .
\]
The second inequality follows by applying midpoint convexity to \(x,x+2U\) and taking expectations. Consequently \(-0.998x^{3/2}<R_1(x)<0.475x^{3/2}\) throughout the same real interval.

All bounds in (2) use the worst endpoint for each monotone factor. The [256-bit interval check](check_additive_prime_area.py) and [resulting enclosures](ADDITIVE_PRIME_AREA_CHECK.json) certify the uniform numerical constants using python-flint 0.9.0. The kernel and proper-power comparison above are paper arguments. This finite reduction leaves the eventual sign open.
