# Translated power grids for the complete centered prime response

**DERIVED on paper, 19 November 2026.** Fix any power \(\theta>0\). For almost every single grid translation, replacing the prime powers and the continuum in each cell by their common center gives an error of exponential rate at most \(d-\theta/2\), where \(d\) is the actual supremum of the rightward zeta-zero displacements. The complete field on the grid therefore has the same native terminal-window energy rate \(d\). The same translation works at all late real times. The grid stores one signed mass per cell. Obtaining a subexponential bound on the complete signed action of those masses remains **OPEN**.

## The exact data

Let \(j\in C_c^\infty([-S,S])\) be the actual order-zero one-copy OPICA pulse, \(J(z)=\int e^{-zu}j(u)\,du\), and \(d=\max(0,\sup_\rho(\Re\rho-1/2))\) over nontrivial zeros. Put
\[
 d\nu(x)=\sum_{m\ge2}\Lambda(m)\delta_m(dx)-{\bf1}_{[2,\infty)}(x)\,dx,\qquad
 f_t(x)=x^{-1/2}j(t-\log x),\qquad P_c(t)=\int f_t\,d\nu .
\]
All prime powers have their original \(\Lambda(m)\). For \(t>\log 2+S\), the continuum integral is \(e^{t/2}J(1/2)=0\), so \(P_c(t)\) equals the literal native field \(P(t)\). Changing the initial interval gives an entire correction to the unilateral Laplace transform. [Native source and its transform](../step4-duration-2026-11-19/jets/SINGLE_SCALAR_CAYLEY.md)

For \(a\in[0,1)\) fixed before observing \(t\), take the half-open cells
\[
 I_{k,a}=\{x\ge2:k\le x^\theta+a<k+1\},\qquad
 c_{k,a}=(k+1/2-a)^{1/\theta}
\]
for nonempty cells. Each center is positive, including in the first truncated cell. Set
\[
 P_{a,\theta}(t)=\sum_k f_t(c_{k,a})\,\nu(I_{k,a}),\qquad
 E_a(t)=P_{a,\theta}(t)-P_c(t).
\]
The sum is locally finite in \(t\). Centering means subtracting the *exact length of the same cell* from its full prime-power mass, including any endpoint truncation at 2. The continuum sampled at the cell centers must be included. Through \(x=X\) the representation uses \(O_\theta(1+X^\theta)\) cells. When \(0<\theta<1\), the spacing in the original integer coordinate at \(x\asymp X\) is of order \(X^{1-\theta}\).

## A bound for each harmonic of the centered measure

Let \(W\) be a fixed smooth function compactly supported in \((0,\infty)\), \(X=e^t\), and write \(e(u)=\exp(2\pi i u)\). For \(X\) large enough that the support in \(x\) is above 2, put
\[
 S_h(X;W)=\int W(x/X)e(hx^\theta)\,d\nu(x).
\]
For \(0<|h|\le X^2\) and \(F=|h|X^\theta\), and separately for \(h=0\), the bounds are
\[
 |S_h|\ll_{W,\theta,\eta} X^{1/2+d+\eta}\sqrt F,\qquad
 |S_0|\ll_{W,\eta} X^{1/2+d+\eta} \quad(\eta>0).                 \tag{1}
\]
For all \(h\), including arbitrarily large frequencies, elementary integer counting gives \(|S_h|\ll_W X\log(2X)\). The constants in this note may depend on the fixed pulse, smoothing, power and margin, and are independent of horizon and harmonic in the indicated ranges.

Here is a contour proof of (1). When \(1/2+d<1\) choose \(\sigma\) strictly between \(1/2+d\) and \(\min(1,1/2+d+\eta)\), leaving a fixed margin to absorb logs. Mellin inversion initially above 1 gives the \(\Lambda\) sum with multiplier \(-\zeta'/\zeta(s)\). Moving to \(\Re s=\sigma\) crosses only its pole at 1, whose residue is exactly the continuum integral. On this line the logarithmic derivative is \(O_\sigma(\log(2+|\Im s|))\), with dependence also on the distance from the zero supremum. Indeed \(G(s)=(s-1)\zeta(s)/(s+2)\) is zero-free in \(\Re s>1/2+d\) and polynomially bounded in any closed substrip there by Euler summation. Choose zero-free disks centered at \(2+i\tau\) with outer radius slightly larger than \(2-\sigma\), still inside this half-plane. At their centers a branch of \(\log G\) is uniformly bounded by the absolutely convergent Euler logarithm and the rational factor. Borel–Carathéodory and Cauchy's estimate on successively smaller disks bound \(G'/G\) by \(O_\sigma(\log(2+|\tau|))\), which gives the asserted bound away from 1. These bounds also justify the contour shift with the smooth Mellin transform.

In \(u=\log(x/X)\) the Mellin transform, apart from \(X^s\), is the Fourier transform of \(e^{\sigma u}W(e^u)e(hX^\theta e^{\theta u})\). Its \(L^2\) norm is bounded independently of \(h,X\) by Plancherel. On \(|\Im s|\le C_{W,\theta}(1+F)\), Cauchy–Schwarz bounds its \(L^1\) norm by \(O(\sqrt{1+F})\). Outside that interval repeated integration by parts gives \(O_N((1+|\Im s|)^{-N})\): the phase derivative has magnitude comparable to \(|\Im s|\), and each higher phase derivative is \(O_{N,\theta,W}(F)\). The logarithmic cost is absorbed by the margin since \(|h|\le X^2\). At \(h=0\) the smooth transform decays rapidly independently of \(X\). This proves (1). If \(d=1/2\), the elementary bound already proves (1) for every \(\eta>0\). This argument uses the definition of the actual supremum and does not assume its value or attainment. [Mellin inversion and Plancherel conventions](https://dlmf.nist.gov/1.14)

## Translation average, with the entire Fourier tail

Write \(v=x^\theta\), \(b(u)=1/2-\{u\}\), and
\[
 \Phi_t(v)=v^{-1/(2\theta)}j(t-\theta^{-1}\log v)
          =X^{-1/2}G_j(v/X^\theta),\quad
 G_j(z)=z^{-1/(2\theta)}j(-\theta^{-1}\log z).
\]
The argument change is exactly \(v\mapsto v+b(v+a)\), with \(|b|\le1/2\). Taylor expansion through \(L\ge1\) gives a \(k\)-th error summand, \(1\le k\le L\),
\[
 D_k(a,t)=X^{-1/2-k\theta}\int W_k(x/X)b(x^\theta+a)^k\,d\nu(x),
 \qquad W_k(y)=G_j^{(k)}(y^\theta)/k!.
\]
Each \(W_k\) is fixed and smooth. The Taylor remainder is \(O_{L,j,\theta}(X^{1/2-(L+1)\theta}\log(2X))\), uniformly in \(a\). The intermediate evaluation requires \(v\) to lie within \(1/2\) of the scaled compact support, hence \(x\asymp X\) with fixed constants. Counting the total mass of \(d\psi+dx\) on this enlarged interval proves the bound.

The Fourier coefficients \(b_{k,h}\) of the periodic function \(b^k\) satisfy \(|b_{k,h}|\ll_k(1+|h|)^{-1}\) by bounded variation. Translation and Fubini give the exact \(h\)-th coefficient of \(D_k(\,\cdot\,,t)\) as \(X^{-1/2-k\theta} b_{k,h}S_h(X;W_k)\). This coefficient identity requires only a finite measure on the support. Parseval is applied in the translation variable. No pointwise Fourier convergence at a jump of the prime distribution is needed.

Take \(H=\lfloor X^2\rfloor\). Before the factor \(X^{-1/2-k\theta}\), the estimates for the three pieces of the root mean square are
\[
 \begin{array}{ll}
 h=0: & O(X^{1/2+d+\eta}),\\
 1\le |h|\le H: &
 O\!\left(X^{1/2+d+\eta+\theta/2}
       \big(\sum_{1\le h\le H}h^{-1}\big)^{1/2}\right),\\
 |h|>H: & O\!\left(X\log(2X)
       \big(\sum_{h>H}h^{-2}\big)^{1/2}\right)
       =O(\log(2X)).
 \end{array}
\]
The last line retains every harmonic, using the elementary bound independent of \(h\). After normalization the tail is \(O(X^{-1/2-k\theta}\log(2X))\). Choose \(L\) with \((L+1)\theta>(1+\theta)/2\), then absorb logarithms by first taking \(\eta\) sufficiently small. The largest exponent among the nonzero Taylor terms occurs at \(k=1\). For every \(\epsilon>0\) this gives
\[
 \|E_\bullet(t)\|_{L^2(da)}
       +\|\partial_t E_\bullet(t)\|_{L^2(da)}
 \ll_{j,\theta,\epsilon} e^{(d-\theta/2+\epsilon)t}.             \tag{2}
\]
The derivative follows by running the same proof for \(j'\). At fixed \(a\) both the grid and its masses are independent of time, so this is the derivative of the actual error.

## A single fixed grid for all times

The unit-interval Sobolev inequality gives
\[
 \int_0^1\sup_{N\le t\le N+1}|E_a(t)|^2\,da
 \ll\int_N^{N+1}\int_0^1(|E_a(t)|^2+|\partial_tE_a(t)|^2)\,da\,dt
 \ll_{j,\theta,\epsilon} e^{2(d-\theta/2+\epsilon)N}.
\]
Markov's inequality with threshold \(e^{(d-\theta/2+2\epsilon)N}\) gives a summable exceptional measure \(O_\epsilon(e^{-2\epsilon N})\). Borel–Cantelli and a countable intersection over margins yield, for almost every fixed \(a\),
\[
 \boxed{\quad E_a(t)=O_{j,\theta,a,\epsilon}
          (e^{(d-\theta/2+\epsilon)t})
          \quad\text{for every }\epsilon>0,\ t\to\infty.\quad}   \tag{3}
\]
A single full-measure set works for any specified countable set of exponents, for example all positive rational \(\theta\), and for all fixed derivative orders by repeating the proof. There is no choice of translation depending on \(t\), a candidate zero or a terminal window. This argument does not certify an individually prescribed translation such as \(a=0\).

## Consequences, exact scope and the one-sided target

* The unilateral Laplace transform of the discrepancy is holomorphic on \(\Re z>d-\theta/2\), by (3) and absolute convergence locally uniformly there. In that half-plane the grid field has the same poles with the same principal parts as the native transform wherever the latter is continued. This claim uses the complete normalized field; no inverse estimate or sign claim on an individual mass is involved.
* For each \(C>1\), the native theorem gives rate \(d\) for \(\log(1+\|P\|_{L^2[T-C\log T,T]}^2)/(2T)\). If \(d>0\), (3) bounds the norm of the error in that window by \(\exp((d-\theta/2+\epsilon)T+O(\log T))\). With \(\epsilon<\theta/2\), the triangle and reverse triangle inequalities preserve the positive rate. If \(d=0\), (3) gives a decaying error and the nonnegative log rate has limsup zero. Thus the *same terminal-window limit* holds for \(P_{a,\theta}\). If \(d<\theta/2\), the error itself is in \(L^1\cap L^2\) on the positive half-line. [Exact merged window theorem, order zero](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeWindowRate.lean#L1154-L1158)
* The grid error made on the proper prime powers alone is \(O_{j,\theta}(X^{-\theta}\log^2(2X))\) uniformly in \(a\): their total \(\Lambda\)-weight on \(x\asymp X\) is \(O(\sqrt X\log^2(2X))\), and the per-term change is \(O(X^{-1/2-\theta})\). This controls their *rounding discrepancy*. Their original contribution stays in the native field.
* The theorem bounds the absolute **change** in the response. A rightward zero would produce the same positive growth rate in both fields, so this estimate alone agrees with that alternative. An independent upper on the complete centered grid action, e.g. a subexponential energy upper on a cofinal sequence of the same terminal windows, would oppose the native lower. Such an upper must use the actual signed masses jointly. Cell counts, a geometric support bound, or the small error between the two fields do not supply it. The original one-sided Step 4 inequality and RH remain **OPEN**.

The arithmetic mass and radius estimates, contour shift, phase Parseval identity and exceptional-set argument above are paper deductions. The cited native theorem concerns the original source. No new Lean declaration or CI result validates the translated-grid comparison.
