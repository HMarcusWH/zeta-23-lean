# The signed graph at the first active rough divisors

At the fixed cutoff \(Y=10^7\), we can evaluate the **actual** distinct-divisor covariance including every signed weight, every prime power, and the full smooth source. At four centers just after distinct rough divisors begin contributing, its signs are \(-,-,+,+\). This disproves a universal pointwise negative sign from the graph structure. The times here are \(t=\log X\), all below 18. They lie well before the late-window sign estimates.

| \(X\) | Prime and prime-power atoms | Rough channels | Nonzero ordered matrix entries | Enclosure of \(s^{10}(P^2-E_Y)(\log X)\) |
|---:|---:|---:|---:|---:|
| 21,000,000 | 609 | 323 | 497,743 | \(-385.85\pm0.00692\) |
| 23,000,000 | 683 | 340 | 580,040 | \(-110.64\pm0.00610\) |
| 25,000,000 | 721 | 360 | 648,720 | \(+277.71\pm0.00540\) |
| 29,000,000 | 817 | 422 | 867,632 | \(+64.75\pm0.00679\) |

## Construct the graph from the actual arithmetic

Write \(s=1/4096\) and \(X=e^t\). For these observations \([Xe^{-s},Xe^s]\subset (2Y,3Y)\). A squarefree rough divisor contributing to \(S_r V_Y\) is either 1 or one prime \(p>Y\). In the latter case \(m/r\) can only be 2 among contributing integer-drive coefficients, since the coefficient at 1 vanishes. The small-prime filter does not change the coefficient at 2. Thus on the pulse window the exact integer coefficient vector of the full field is \(v_m=\Lambda(m)/\sqrt m\), the rough group \(p\) has vector \(-u_m e_m\) at \(m=2p\) with \(u_m=\log(2)/\sqrt m\), and the group 1 has vector \(v+u\). The supports of \(v\) and \(u\) are disjoint. With \(D=\operatorname{diag}(u_m^2)\), the exact signed matrix is
\[
 K=vv^\top-(v+u)(v+u)^\top-D=-vu^\top-uv^\top-uu^\top-D .
\]
It acts on the source vector \(j(t-\log m)\). Every nonzero matrix entry is negative. Nevertheless the matrix has one positive eigenvalue whenever \(v\ne0\) and at least one rough group contributes. Indeed \(-D-uu^\top\) on the rough indices is negative definite. Its Schur complement in the single direction \(v/\|v\|\) is \(\|v\|^2 u^\top(D+uu^\top)^{-1}u>0\); vectors supported on the genuine Mangoldt indices orthogonal to \(v\) are exactly the remaining nullspace. The finite calculation shows the actual translated source attains both signs.

## Enclose the source at every active atom

Use \(h(x)=s^5j(sx)\) for \(|x|\le1\). The smooth zero extension of its underlying density has a Fourier series of period 2. Its nonconstant cosine coefficients are
\[
 B_k=((\pi k)^2+s^2/4)^2
       \prod_{d\ge1}\operatorname{sinc}\bigl(\pi k/[d(d+1)]\bigr).
\]
The constant term is \(s^4/32\), and the first box makes every nonzero even coefficient vanish. For each retained odd \(k\le511\), truncating the box product at 1024 incurs error at most the absolute retained coefficient times \((\pi k)^2/(18\cdot1024^3)\), by telescoping with \(|1-\operatorname{sinc}x|\le x^2/6\). For the omitted frequencies use the first 18 factors and \(|\operatorname{sinc}x|\le1/|x|\). The remaining absolute tail is at most
\[
 (\pi^2+s^2/4)^2\frac{18!19!}{13\pi^{18}\,511^{13}}.
\]
Together these bound the uniform scaled-source error by 0.000248. Directed Arb intervals enclose every coefficient, every log prime weight, every active source value, and both direct and factored computations of the quadratic. The calculation used all prime powers in each certified support interval. [Source](check_graph.py) · [Interval results and graph counts](OBSERVATIONS.json) · [Repository source family](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeSourceFamily.lean)
