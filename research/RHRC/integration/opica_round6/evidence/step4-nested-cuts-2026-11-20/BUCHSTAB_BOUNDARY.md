# Signed cost of the cap in an alternating Buchstab calculation

**DERIVED on paper.** This separate computation concerns the *original* squarefree rough source, on some count layers the real native matching subsequently retires with their opposite-sign partners. It resolves the cap-crossing term in one signed insertion identity. It makes no opposite-sign choice for the unmeasured part of the survivor sum.

Use the pinned source, \(U,X,y,J,H,\Phi\) and \(\nu\) of [the survivor calculation](NEUTRAL_PRIME_TRANSPORT.md). Fix \(0<\delta<.3\), \(u>64\) with \(u\delta>8\), \(z=U^{1/u}\) and \(A=\sum_{y<p\le z}p^{-1}\). For each positive integer \(n\) use its unique split at \(z\). For each \(k\) let \(C_k(J)\) be the complete signed charge of \(n=dm\in J\) with squarefree marked factor \(d\le U^\delta\), \(\omega(d)=k\), all \(p\mid d\) in \((y,z]\), and all \(p\mid m\) exceeding \(z\). All allowed numbers and parities of large factors are retained, with their original signs.

### The complete large-cofactor density

Set \(h(t)={\bf1}_{t\ge1}/t\). For fixed \(m\)-product order \(j\ge1\), replace the true prime factors successively by \(dt/\log t\), summing ordered distinct tuples with weight \(1/j!\). The endpoints and lower cutoff \(z\) leave any one frozen-primes slice an interval. The reciprocal mass of the other primes or continuous prime measures is \(O_u(1)\), and every coordinate is \(\ge U^{1/u}\). At most \(u+1\) orders occur. The same section proof as (1) in the linked note costs \(O_u((U/d)e^{-c_u\Phi(\log U)})\) including the cut endpoints. Repeated coordinates in ordered true tuples cost \(O_u((U/d)/z+\sqrt{U/d})\): sum \((2U/d)/p^2+1\) up to \(\sqrt{2U/d}\) and note that each integer has at most \((u+1)!\) ordered representations at fixed order. The count of admissible \(m=1\) is zero because \(d\le U^\delta\).

Pass to log-prime variables in units of \(\log z\). The signed main term per unit \(dx/d\) is \(W(v)/\log z\), \(v=\log(x/d)/\log z\), where
\[
 W(v)=\sum_{j\ge1}(-1)^j h^{*j}(v)/j!.
\]
There are finitely many nonzero summands on each compact interval. Weighting a \(j\)-fold convolution by the sum of its coordinates gives \(v h^{*j}(v)=j({\bf1}_{[1,\infty)}*h^{*(j-1)})(v)\), with \(h^{*0}\) the atom at zero. Thus \(vW(v)=-1-\int_1^{v-1}W(s)\,ds\) for \(v\ge1\), with the integral set to zero below 2. Writing \(vW(v)=-\rho(v-1)\) gives \(\rho=1\) on \([0,1]\), \(t\rho'(t)=-\rho(t-1)\) for \(t>1\). Its positivity follows from \(t\rho(t)=\int_{t-1}^{t}\rho(s)\,ds\) and a first-zero argument on each bounded range. Hence the true complete continuum kernel has a definite negative sign for every allowed \(d\). The values of \(\rho\) may be very small when \(u\) is large; \(u\) is fixed in this assertion.

Let \(l=\log x/\log U\), \(\theta(d)=\log d/\log U\), and
\[
 K_x(a)={\rho(u(l-a)-1)\over l-a}{\bf1}_{0\le a\le\delta},\qquad
 S_k(x)=\sum_{\omega(d)=k,\ p\mid d\implies y<p\le z}^{\rm squarefree}
               {K_x(\theta(d))\over d}.
\]
The cap is enforced by the kernel. On \([0,\delta]\) it has positive upper and lower constants and a uniform Lipschitz bound depending on \(u,\delta\); it jumps at the upper endpoint. The charge is
\[
 C_k(J)=\frac{(-1)^{k+1}}{\log U}\int_J S_k(x)\,dx
     +O_{u,\delta}\big(U e^{-c\Phi(\log U)} B_k\big),\qquad B_k=A^k/k!.
\]
Here \(\sum_{\omega(d)=k}1/d\le B_k\), and the repeated-coordinate power errors are absorbed. Uniformly for \(k=A+O_K(\sqrt A)\), \(S_k(x)\asymp_{u,\delta,K} B_k\). To see the lower, draw \(k\) prime indices independently with mass \(1/(pA)\) on the marked interval. The probability of a repetition is at most \(\binom k2\sum_{p>y}(pA)^{-2}=o(1)\). The expected \(\theta\) of their product is \((k/A)(1/u+o(1))\) by the prime harmonic log moment. Markov and \(u\delta>8\) keep more than half the weight inside the cap for every sufficiently late shell. Dividing the distinct ordered tuples by \(k!\) then gives the lower. This finite probability argument evaluates reciprocal sums over prime choices, independently of any assumption on the original integer signs.

### Inserting the next marked prime and retaining the boundary

Counting the possible inserted factor with its multiplicity gives
\[
 (k+1)S_{k+1}(x)=A S_k(x)+O_{u,\delta,K}(B_k).
\]
To check this, write \(v_p=\log p/\log U\) and compare \(K_x(\theta+v_p)\) with \(K_x(\theta)\) for each marked \(p\) and \(p\nmid d\). The Lipschitz cost is \(O(B_k\sum_p v_p/p)=O(B_k)\). The forbidden repetitions contribute \(O(k B_k/y)\). It remains to handle the entire crossing \( \delta-v_p\le \theta(d)\le\delta\), even when no factor of \(d\) is comparable to the whole product. Since \(v_p\le1/u<\delta/2\), multiply its indicator by the upper bound \(2\log d/(\delta\log U)\). Expand \(\log d=\sum_{q\mid d}\log q\) exactly and write \(d=eq\). For each fixed \(e\) with \(k-1\) marked factors, the eligible \(q\)'s lie in a prime interval of log width at most \(v_p\log U\), truncating at 2 if necessary. The uniform elementary prime Mertens estimate \(\sum_{a<q\le b}(\log q)/q\ll 1+\log(b/a)\) holds for \(2\le a\le b\). It yields actual crossing mass
\[
  \sum_{d:\,\omega(d)=k,\ \delta-v_p\le\theta(d)\le\delta}\frac1d
      \ll_\delta B_{k-1}(v_p+1/\log U).
\]
The factor \(B_{k-1}/B_k=k/A\) is bounded. Summing this term with \(1/p\) costs \(O(B_k)\), as claimed. No layer overshooting \(U^\delta\) has been returned to the permitted population.

The resulting ratio \(S_{k+1}(x)/S_k(x)=A/(k+1)+O(1/A)\) holds uniformly near the center. Stirling and \(e^A\asymp_u\log U/\log y\) give \(B_k\asymp_{K,u}\log U/(\sqrt A\log y)\). Hence for \(H\ge U\exp[-(\log U)^\nu]\),
\[
 (-1)^{k+1} C_k(J)\asymp {H\over\sqrt A\log y},
 \qquad |C_k(J)+C_{k+1}(J)|\ll {H\over A\log y}.
\]
Uniformity at this precision follows from \(Ue^{-c\Phi(\log U)}/H=o((\log U)^{-A'})\) for any fixed \(A'>0\).

### Which labels have been paid, and where the residual lives

Fix the path constant \(K_0\) of the native selector. Choose an even number of consecutive integers covering \([A-(K_0+3)\sqrt A,A-(K_0+2)\sqrt A]\) up to at most two endpoints. For all sufficiently large \(U\) any such \(d\) violates the native running-count threshold at \(v=z\), since its original variance parameter is \(1+\sum_{y<p\le2U}1/p=A+O_u(1)\). Thus they are genuine targets of the selector. Each parity subwindow has absolute signed charge \(\asymp H/\log y\), with opposite signs, while the union's true signed charge is \(O(H/(\sqrt A\log y))\). At original levels below the displayed \(H\) cutoff, the bound by \(H\) per node gives a negligible contribution to the squared-energy upper, as in the primary note. On every base the matched endpoints of the **full** target set have total charge zero exactly; all other targets and the actual spent partners therefore compensate this window's true signed charge with its negative. The local formula concerns mark layers on arbitrarily late cutoffs. The finite control in this folder tests the exact factor recursion at one cutoff and retains its own explicitly identified partners. The all-late estimate, the actual incumbent survivor sum and the critical cofinal estimate have distinct certification requirements. Step 4 remains **OPEN**.
