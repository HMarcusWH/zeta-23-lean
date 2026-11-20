# The native cut has a rigorously transverse zero

**Paper calculation, 19 November 2026.** Write \(s=1/4096,\ a=s/2=1/8192\). The cumulant of the actual one-copy source has a simple zero at physical log ratio \(\Delta_*=s u_*\) with
\[
 3\cdot10^{-33}<1-u_*<2\cdot10^{-27}.
\]
The small offset has a definite sign. This follows from the first uniform factor of the genuine infinite sinc product. The accompanying script checks the rational bounds.

## Split the source on its first box

In units of \(s\), let \(q_0(x)=s q_s(sx)=\mathbf1_{[-1/2,1/2]}*r\). The remaining even probability density \(r\) is smooth and supported on \([-1/2,1/2]\): its factors are uniforms of half-widths \(1/(k(k+1))\) for integers \(k\ge2\). It has smooth density, since arbitrarily many of these factors can be differentiated once as measures, leaving an undifferentiated continuous density. This factorization also follows from equality of characteristic functions for the convergent sum of independent uniforms. [Exact source widths and infinite sinc product](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/CCM/UniversalSincDetector.lean) · [Original one-copy source](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/CCM/OriginalSincNativeSource.lean)

Set \(j_0=(D^2-a^2)^2q_0,\ g_0(x)=e^{-ax}j_0(x)\) and
\[
 K_0(u)=\iint_{|x-y|\le u} g_0(x)g_0(y)\,dx\,dy .
\]
The physical source satisfies \(j_s(sx)=s^{-5}j_0(x)\), so the physical cumulative \(K(su)=s^{-8}K_0(u)\). Define
\[
 G(x)=\int_{-1/2}^x(D^2-a^2)^2r(v)\,dv
 =r'''(x)-2a^2r'(x)+a^4\int_{-1/2}^x r(v)\,dv .
\]
For \(-1/2\le x\le1/2\) the left half of \(j_0\) is \(j_0(x-1/2)=G(x)\), and its right half is \(j_0(x+1/2)=a^4-G(x)\).

## Exact signed value at the half-width threshold

Write \(H(x)=e^{-ax}G(x)\), \(R(z)=\int e^{-zx}r(x)dx\). Because \(\int g_0=0\), the near cumulative at one equals minus the far cumulative. All far pairs have one coordinate in each half, with \(x<y\) in their respective translated coordinates (plus the reversed ordering). Thus
\[
 K_0(1)=\bigg(\int H(x)dx\bigg)^2
 -2a^4\int_{-1/2}^{1/2}e^{-ay}\int_{-1/2}^{y}H(x)\,dx\,dy .
\]
Integration by parts yields \(\int e^{-zx}G'=(z^2-a^2)^2R(z)=a^4e^{-z/2}+z\int e^{-zx}G\). At \(z=a,2a\),
\[
 \int H=-a^3e^{-a/2},\qquad \int e^{-2ax}G=(a^3/2)(9R(2a)-e^{-a}).
\]
The double integral above is \(\frac1a(\int e^{-2ax}G-e^{-a/2}\int H)\). Consequently
\[
             K_0(1)=-9a^6R(2a),\qquad 1\le R(2a)\le e^a .
\]
The lower bound on \(R\) uses the even unit-mass density. This explicitly resolves the sign that would be lost at ordinary plotting precision.

## Uniform slope and isolation

Differentiate the cumulative to get \(K_0'(u)=2\int g_0(x)g_0(x+u)dx\), whence
\[
 K'_0(1)=2\int_{-1/2}^{1/2} e^{-2ax}\left(\frac{a^8}{4}-(G(x)-a^4/2)^2\right)\,dx .
\]
Testing \(G-a^4/2\) against \(x^3\) gives \(-6+6a^2\int x^2r+a^4\int x^3\int_{-1/2}^xr\), by integration by parts. Its absolute value exceeds 5. Since \(\int_{-1/2}^{1/2}x^6dx=1/448\), Cauchy–Schwarz gives \(\int(G-a^4/2)^2>11200\), and hence \(K'_0(1)<-22000\).

Differentiating once on each of the first \(m\) uniform factors and bounding the next box density gives
\[
 \|q_0^{(m)}\|_\infty\le m!(m+1)!(m+1)(m+2)/2 .
\]
Use \(m=0,\ldots,5\) and \(e^a\le1/(1-a)\) to obtain \(\|g_0\|_\infty<43300\), \(\|g'_0\|_\infty<1820000\). Cauchy–Schwarz and the support of length 2 give
\(\sup|K'_0|<8\cdot10^9,\ \sup|K''_0|<4\cdot10^{11}\).
In particular throughout \(1-10^{-8}\le u\le1\) the derivative is less than \(-16000\). The exact value at one, the slope bounds and the intermediate value theorem isolate the simple zero with the displayed interval for \(1-u_*\). Every cutoff constant used here precedes the arithmetic horizons. [Exact scalar verification](TRANSVERSE_CONSTANTS.json)
