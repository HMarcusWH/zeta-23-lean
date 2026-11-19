# The genuine divisor sum at the cut comparison

**Paper calculation, 19 November 2026.** This tests what additional information the literal Mangoldt identity gives after identifying the two crossing locations. The same late energy can be written using only polynomially many values of the inner divisor. The outer signed Möbius sums still have to be estimated together.

For the one-copy \(j\) from the graph reduction, define the full integer drive
\[
 U(u)=\sum_{k\ge2}(\log k)k^{-1/2}j(u-\log k).
\]
The finite divisor identity \(\Lambda=\mu*\log\) gives, with no limiting interchange,
\[
 P(t)=\sum_{a\le e^{t+s}}\frac{\mu(a)}{\sqrt a}U(t-\log a).
\]
Put \(z=e^u,\ F(y)=y^{-1/2}j(-\log y),\ G(y)=\log(y)F(y)\), extended by zero. They are supported on \([e^{-s},e^s]\). The two half-pole moments \(J(1/2)=J'(1/2)=0\) imply \(\int F=\int G=0\). The exact sampling equation is \(U(u)=z^{-1/2}\{u\sum F(k/z)+\sum G(k/z)\}\).

The native Gevrey derivative bound and compact support give \(\|F^{(m)}\|_1+\|G^{(m)}\|_1\le C B^m(m!)^2\). For details, on this compact interval the normalized derivatives of the analytic change \(-\log y\) are bounded by \(D^\ell\) at degree \(\ell\). In the chain rule after division by \(m!\), the contribution at degree \(k\) of the outer derivative is bounded by \(C B_0^k k!\binom{m-1}{k-1}D^m\). Summing using \(k!\le m!\) proves the stated bound after increasing \(B\). Multiplication by the analytic factors costs another fixed increase. The extensions are smooth because the native source is flat at its support endpoints.

Poisson summation for compact smooth functions eliminates the zero Fourier coefficient exactly. Integration by parts \(m\ge2\) times then gives
\[
 \left|\sum_k F(k/z)\right|+\left|\sum_k G(k/z)\right|
 \le C' z\frac{B^m(m!)^2}{(2\pi z)^m}\sum_{k\ge1} k^{-m}.
\]
Take \(m=\lfloor\sqrt{\pi z/(2B)}\rfloor\), using a fixed adjustment for bounded \(z\ge1\). Thus \(|U(\log z)|\le C(1+\log z)\sqrt z\, e^{-c\sqrt z}\). All constants are fixed by the genuine seed.

Fix any requested decay \(A>0\). At all terminal quadrature nodes \(t_i\in[n-2\log n,n]\) choose one \(K=K_{A,j}\) with \(c\sqrt K>A+1\). Then
\[
 \sum_{a\le e^{t_i}/(K n^2)} a^{-1/2}|U(t_i-\log a)|
 \ll_j e^{n/2}(1+n)^2 e^{-c\sqrt K\,n}\ll_{A,j} e^{-An}.
\]
The elementary bound follows by replacing the remaining sum over \(a\) by the harmonic series. On the retained side \(a>e^{t_i}/(Kn^2)\), compact support forces \(k\le e^s K n^2\). In particular with
\[
 B_i=\sum_{2\le k\le e^sKn^2}\frac{\log k}{\sqrt k}
       \sum_{a>e^{t_i}/(Kn^2)}
       \frac{\mu(a)}{\sqrt a}\,j(t_i-\log(ak))
\]
we have \(P(t_i)=B_i+O_{A,j}(e^{-An})\) uniformly. The sum over \(a\) is finite by support. With \(A=2\), Chebyshev gives \(|P(t_i)|\ll_j e^{n/2}\) and consequently
\[
 Q_n=\sum_i w_i B_i^2+O_j(\log(n)e^{-3n/2}).
\]
The square retains all signed products between the \(k\) channels. The cut \(a>e^{t_i}/(Kn^2)\) and the original weights depend on the same sample. A change to an unrelated Möbius packet would lose the identity.

Here is the precise connection to the other graph calculation. Independently, the complete ordinary-prime energy equals the ordinary-prime diagonal plus \(B_n(x_0)+\sum_{\log(q/p)>x_0}w_{pq}\), with \(|B_n(x_0)|\ll_j n^4\log(n)e^{-n}\). Proper-power restoration compares its square root to \(\sqrt{Q_n}\) with additive \(O_j(\sqrt{\log n})\). Thus an all-positive-exponent cofinal upper for the signed divisor quadratic \(\sum w_i B_i^2\), or for that far-pair sum, reaches the same native closing implication. This derivation applies the smoothing cancellation to the complete field. A sharp restriction \(\log(q/p)>x_0\) inside the divisor transform would introduce boundary terms and needs a separate proof.

**Attempted independent bound.** Chebyshev and the support length give the crude size \(O_j(e^{n/2})\) per full field. Treating each \(k\) channel by absolute values leaves exponentially many active \(a\) (already for \(k=2\), for which the retained interval has length comparable to \(e^{t_i}\)). An upper on the absolute Möbius count therefore leaves exponential cost. The external zero ceiling bounds the full squared observation with exponent \(2b\). The two-cumulative-curve argument gives a tiny arithmetic prefix but does not bound the remaining long-ratio Möbius correlations. No independent subexponential estimate for their signed sum is established here.

[Native integer–prime convolution](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/CCM/NativeIntegerPrimeConvolution.lean) · [One-copy source and history](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeSourceFamily.lean)
