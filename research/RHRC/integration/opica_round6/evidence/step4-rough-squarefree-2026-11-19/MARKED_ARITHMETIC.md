# Sensitivity of the complete source to a rough prime count

**DERIVED on paper, 19 November 2026. Step 4 and RH remain OPEN.** Count the distinct prime divisors above \(y=T^2\) in each squarefree Möbius row. After adding every signed row, multiplying its weight by that count produces a response asymptotic to \(M e^{T/2}/T^2\), with a strictly positive constant fixed by the source. The unmarked sum is the genuine prime field \(Z(T)\). This calculation determines the first derivative with respect to a change of weights. The independent bound on the value at the original weights remains open.

## The genuine fields

Use the frozen real compact profile \(h\) with bilateral transform \(H(s)=(s^2-1/4)^2Q(s)^2\), where \(Q\) is the transform of the nonnegative normalized seed \(q\). Define
\[
 U(t)=\sum_{n\ge2}\frac{\log n}{\sqrt n}h(t-\log n),\qquad
 Z(t)=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}h(t-\log n).
\]
The support radius of \(h\) is smaller than \(\log 2\), so both fields vanish for \(t\le0\). The exact divisor identity \(\mu*\log=\Lambda\) gives \(Z(T)=\sum_d\mu(d)d^{-1/2}U(T-\log d)\) on each finite history. Here \(d\le e^T\), whereas the internal prime-field cutoff also accounts for the fixed support of \(h\). [Native finite histories at the merged revision](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/CCM/NativeIntegerPrimeField.lean) · Fixed source and full integer-drive estimates

Put \(\omega_{>y}(d)=\#\{p\mid d:p>y\}\) and
\[
 F_T(w)=\sum_{d\le e^T}\frac{\mu(d)}{\sqrt d}\,w^{\omega_{>y}(d)}U(T-\log d).
\]
This is a finite real polynomial. Its \(k\)-th coefficient \(Z^{(k)}\) includes every small-prime divisor with its original Möbius sign. Thus \(F_T(1)=Z(T)\) and \(F_T'(1)=\sum_k k Z^{(k)}\).

## The marked sum

For each integer \(d\),
\[
 \mu(d)\omega_{>y}(d)
 =-\sum_{\substack{p>y,\ j\ge1\\p^j\mid d}}\mu(d/p^j).
\]
For a prime of exponent one in \(d\), the corresponding term equals \(\mu(d)\) after the outer minus sign. At an exponent at least two, the last two terms cancel, and earlier terms vanish. Finite convolution gives the exact identity
\[
 F_T'(1)=-\sum_{p>y}\sum_{j\ge1}p^{-j/2}Z(T-j\log p).
 \tag{1}
\]
Every prime power in the marked identity has been retained.

Set \(K(t)=e^{-t/2}Z(t)\). The quantitative prime number theorem and compact smoothness give \(|K(t)|+|K'(t)|\ll_h e^{-c\sqrt t}\) for \(t\ge1\). Indeed, in the Stieltjes integral for \(Z\), replacing \(d\psi(x)\) by \(dx\) gives \(e^{t/2}H(1/2)=0\) for all sufficiently late \(t\). Integrating the remainder by parts only uses \(x\) within fixed multiples of \(e^t\). The derivative uses \(h'\), whose corresponding moment also vanishes. In particular, all polynomial moments of \(K\) converge absolutely. [Unconditional quantitative prime number theorem](https://arxiv.org/abs/2204.02588)

For real \(s>1/2\), absolute convergence gives
\[
 \widehat U(s)=-H(s)\zeta'(s+1/2),\qquad
 \widehat Z(s)=-H(s)\frac{\zeta'}{\zeta}(s+1/2).
\]
Near \(s=1/2\), write \(v=s-1/2\). The double source zero and the simple zeta pole give \(\widehat U(1/2)=M=Q(1/2)^2>0\) and \(\widehat Z(1/2+v)=Mv+O(v^2)\). The moment bounds justify taking the value and the right derivative under the integral. Hence
\[
 \int_0^\infty K(u)\,du=0,\qquad \int_0^\infty uK(u)\,du=-M.
 \tag{2}
\]

After division by \(e^{T/2}\), the \(j=1\) sum inside (1) is \(\sum_{p>y}p^{-1}K(T-\log p)\). Partial summation of the quantitative prime number theorem gives \(\sum_{p\le e^r}p^{-1}=\log r+B+O(e^{-c\sqrt r})\) for large \(r\), with a possibly smaller \(c>0\). On \(\log y<r<T/2\) the test \(K(T-r)\) and the integral are exponentially small in \(\sqrt T\), up to logarithmic factors. On \(T/2\le r\le T\) integration by parts costs a bounded total variation since \(K'\in L^1\). It follows, using (2), that
\[
 \sum_{p>y}\frac{K(T-\log p)}p
 =\int_0^{T-\log y}\frac{K(u)}{T-u}\,du+O(e^{-c'\sqrt T})
 =-\frac{M}{T^2}+O_h(T^{-3}).
\]
For the final equality expand the denominator on \(u\le T/2\); the absolute second moment pays the remainder. The tail \(u>T/2\) is negligible since \(T-u\ge\log y\).

The normalized \(j\ge2\) sums involve \(p^{-j}K(T-j\log p)\). For \(j\log p\le T/2\) use the decay of \(K\) and sum \(p^{-j}\) absolutely. On the complement use \(p^{-j}\le e^{-T/8}p^{-3j/4}\), whose double sum after removal of the exponential converges. Restoring the outer minus sign yields
\[
 \boxed{\displaystyle F_T'(1)=\frac{M e^{T/2}}{T^2}
          +O_h\!\left(\frac{e^{T/2}}{T^3}\right).}
\]

## What this determines

* **Sensitivity to uniformly small relative errors.** For any fixed \(A>1\), the factors \(1+T^{-A}\omega_{>T^2}(d)\) converge uniformly to 1 over the whole history. Indeed \(\omega_{>T^2}(d)\le T/(2\log T)\). With these modified factors the sum equals \(Z(T)+T^{-A}F_T'(1)\sim M e^{T/2}/T^{A+2}\), since the unmodified \(Z(T)\) is \(O_h(e^{T/2-c\sqrt T})\). This tests a proposed replacement of the genuine weights. It gives no comparable lower bound for \(Z\) itself.
* **A genuine nearby real root.** For \(|w-1|\le T^{-5}\), boundedness of \(U\), the finite history and \(\sum_{d\le e^T}d^{-1/2}\le2e^{T/2}\) give \(|F_T''(w)|\ll_h T^2 e^{T/2}\). Thus \(F_T'\) stays positive throughout that interval for all sufficiently late \(T\), with relative error \(O_h(1/T)\) around \(M e^{T/2}/T^2\). The bound on \(F_T(1)\) gives opposite signs at the interval endpoints. Its unique root \(w_T\) there satisfies
  \[
  |1-w_T|\ll_h T^2 e^{-c\sqrt T},\qquad
  Z(T)=(M+O_h(T^{-1}))\,e^{T/2}(1-w_T)/T^2.
  \]
  An upper on the unweighted absolute source at every positive exponential rate would require correspondingly finer root location. The stretched-exponential estimate falls short. The original cofinal weighted target would require its own estimate on the weighted absolute root displacement.
* **Fixed degrees.** The one-rough and two-rough asymptotics concern \(Z^{(1)}\) and \(Z^{(2)}\) separately. Their small-prime Euler factor is present in both. In the exact full derivative (1), Möbius convolution has already restored \(Z\), and its leading constant is \(M\) without this factor. Taking any fixed number of degree estimates and summing their asymptotic main terms across all degrees would require a separate uniform remainder estimate.

This note contains a paper calculation. The cited Lean file supplies finite-history definitions; the marked asymptotic and the nearby-root statement have no new Lean or CI qualification. The complete original signed upper remains unproved. Current merged-project evidence
