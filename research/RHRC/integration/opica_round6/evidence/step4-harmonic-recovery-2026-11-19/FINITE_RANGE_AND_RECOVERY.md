# Finite coverage of the complete native statistic and recovery of its first harmonic

**DERIVED on paper, 19 November 2026.** The finite bounds below use published arithmetic and exact rational checks. Four finite algebraic lemmas in the accompanying archive were separately compiled with the project's pinned Lean. The published Mertens bound and its transfer here have paper-level qualification.

## The complete sum at the prescribed phase

Let \(N=\lfloor L^{101/100}\rfloor\) and \(\mathcal B_L(0)=\sum_{L<n\le N}|E_L(n)|/n^3\) as in the native criterion. For the prescribed calibration, whenever the nodes exist and every node exceeds \(2L\), for integer \(L<n<2L\) the complete row has the exact formula
\[
 E_L(n)=\sum_{L<j\le n}\mu(j)(n-j)=\int_L^n (M(u)-M(L))\,du .
\]
The original four-node calibration applies from \(L=2\). For a distributed calibration with \(9\mid R,\ 2L<R\le3L\), the formula applies whenever the calibration is defined (in particular, such an \(R\) exists at every \(L\ge9\)). A calibration on a different domain should retain its own domain.

For every such integer \(2\le L\le 6{,}943{,}591{,}429{,}214{,}285\),
\[
 \mathcal B_L(0)<(16\sqrt L)^{-1}.
\]
The upper endpoint is \(\lfloor10^{1600/101}\rfloor\). Its last native site is \(9{,}999{,}999{,}999{,}999{,}998\). The source of numerical coverage is Hurst's exhaustive computation, with the explicit bound \(|M(u)|\le0.571\sqrt u\) on \(33\le u\le10^{16}\). The inference covers every integer cutoff in this range. Hurst also computed individual larger values, which provide no interval extension here. [Hurst, Section 6](https://arxiv.org/abs/1610.08551) · [Explicit inequality (A6)](https://www.tandfonline.com/doi/full/10.1080/10586458.2025.2483942?src=exp-la)

Put \(\lambda=L^{1/100}\le29/20<5/3\). For \(L\ge2048\), every site lies in the first band and \(|E_L(n)|\le 2(0.571)\sqrt n(n-L)\). The function \(t\mapsto(t-L)t^{-5/2}\) increases up to \(5L/3\). Comparing its sum to its integral plus the last term gives
\[
 \sqrt L\,\mathcal B_L(0)
 \le 2(0.571)\left(\frac43-\frac2{\sqrt\lambda}
    +\frac{2}{3\lambda^{3/2}}+\frac{\lambda-1}{L}\right)<\frac1{16}.
\]
The integral term increases with \(\lambda\). The rational upper witness for \(\sqrt{29/20}\) is \(120417/100000\). For \(2\le L<2048\), the elementary bound \(|E_L(L+h)|\le h(h-1)/2\) gives \(\sqrt L\,\mathcal B_L(0)\le {H+1\choose3}/L^{5/2}\), \(H=N-L\). The script checks all 2,046 cases by integer arithmetic. Exact constants and both endpoint powers are in FINITE_RANGE_CONSTANTS.json.

## Literal signed harmonic

Let \(a=24/25,\ c=21/20,\ n=\lfloor cL\rfloor,\ r=\lfloor aL\rfloor\),
\[
 W_L(q)=\frac{\cos(2\pi n/q)}{2q\sin^2(\pi/q)},\quad
 A(t)=\sum_{\substack{q\le t\\(q,6)=1}}\mu(q),\quad
 T_L=\sum_{r<q\le L} (A(q)-A(q-1)) W_L(q).
\]
For \(L\ge100\) and \(r<q\le L\), \(1<n/q\le35/32\). The cosine and the reciprocal of \(q\sin^2(\pi/q)\) both increase with \(q\). For the latter, \(t=\pi/q\) gives \(2t\cot t>1\) since \(2\cos t>1\) and \(\sin t\le t\). Also \(w_L=W_L(L)<0.051L\) by \(\sin t/t\ge1-t^2/6\). The exact Abel identity is
\[
 T_L/w_L=A(L)-\sum_{r\le j<L}p_{Lj}A(j),
\quad p_{Lr}=W_L(r+1)/w_L,\quad
 p_{Lj}=(W_L(j+1)-W_L(j))/w_L\quad(r<j<L).
\]
These weights are nonnegative and sum to 1. The harmonic identity gives
\(A(t)=\sum_{i,j\ge0}M(t/(2^i3^j))\) by Euler factor removal, with zero terms below one. The published bound and the exact table through 32 imply \(|M(u)|\le\sqrt u\) throughout \(u\le10^{16}\). The geometric sum \((1-2^{-1/2})^{-1}(1-3^{-1/2})^{-1}<8.1\) then gives \(|A(t)|\le8.1\sqrt t\). Taking absolute values after Abel proves
\[
 |T_L|<\tfrac56 L^{3/2}\qquad(100\le L\le10^{16}).
\]

## Recovery at arbitrary horizons

For \(q=r+1\), the ratio of the reciprocal sine factors, after writing each as \(q/(2\pi^2)(\sin(\pi/q)/(\pi/q))^{-2}\), is at least \(q/L\), since \(\sin t/t\) decreases with \(t\) here. The cosine ratio is at least \(\cos(3\pi/16)\). Hence \(p_{Lr}\ge a\cos(3\pi/16)>3/4\), and
\[
 \sum_{j<L}p_{Lj}\sqrt{j/L}
 \le 1-\tfrac34(1-\sqrt a)<1-\tfrac3{200}.
\]
The same upper applies with exponent \(\sigma\ge1/2\). For every finite \(X\), put \(S_0=\max_{j<100,\ j\ge1}|A(j)|/j^\sigma\) and \(F_X=\max_{100\le L\le X}|T_L|/(w_LL^\sigma)\). Induction on \(L\) bounds \(\max_{1\le L\le X}|A(L)|/L^\sigma\) by \(\max(S_0,200F_X/3)\). Signed upper or lower versions follow by applying the positive recurrence to \(A\) or \(-A\). Thus the arithmetic problem is the size of the *forcing* \(T_L/w_L\) beyond the finite range. The four locally verified Lean facts cover summation by parts, total history weight, its weighted upper from hypotheses, and the finite induction. The analytic estimate of the defect \(3/200\) is proved above on paper. Origin and zero visibility of the literal harmonic
