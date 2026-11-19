# Squarefree scores in a shrinking window at a prescribed primorial

**DERIVED on paper.** Fix \(2/3<\kappa<1\), \(c>0\), and any fixed \(A>0\). At every sufficiently large real \(z\) put \(h=c z^\kappa\), \(P=\prod_{p\le z}p\) and \(s=\log P=\vartheta(z)\). There are at least \(\exp(c_1 h/\log z)\) distinct squarefree integers \(n\) such that
\[
  s-z^{-A}\le\log n\le s,\qquad
  T_z(n):=\sum_{q\in\mathcal P(n)\,\triangle\,\mathcal P(P)}|q-z|\log q\le C h^2.       \tag{1}
\]
Here \(\mathcal P(n)\) is the set of prime divisors of \(n\), so the sum runs over primes dividing exactly one of \(n,P\). All these integers differ from \(P\) only at primes in \([z-h,z+h]\). The threshold may depend on \(A,c,\kappa\). The positive constants \(c_1,C\) can be fixed independently of \(A\). This is an unconditional statement about ordinary primes at a **prescribed** primorial.

Let \(D(n)=(\log n)^2/2-\sum_{p\mid n}p\log p+2\). At a true stopping point \(z=s\), put \(V=D(P)\). Every integer in (1) has \(D(n)\ge V-Ch^2\). In particular, if \(b\in(1/2,1)\), \(\kappa=(1+b)/2\), and \(V\ge v z^{1+b}\) with a fixed \(v>0\), choose a fixed \(c>0\) such that \(Cc^2<v/2\). Every sufficiently late such primorial has at least \(\exp(c_1h/\log z)\) genuine violations of the squarefree inequality in the interval \([P\exp(-z^{-A}),P]\), all of score at least \(V/2\). The existence of these high positive stops is conditional. The combinatorial estimate (1) holds independently of their existence. [Exact squared-cost identity](squarefree-lean/SquarefreePrimeCost.lean.md) · [High stopping scores from an off-line zero](STOPPED_PRIME_GRAPH.md)

## Local prime supply and mismatch cost

Any fixed subinterval of relative positive length in \([z-h,z+h]\) contains \(\asymp h/\log z\) ordinary primes. Partition it into intervals of equal lengths between \(z^{3/5}\) and \(2z^{3/5}\), possible since \(h/z^{3/5}\to\infty\). Each starts at a point \(x\asymp z\) and lies in the published range \(x^{17/30+\epsilon}\le y\le x^{0.99}\) for a fixed small \(\epsilon>0\). Guth and Maynard's prime-count asymptotic applies uniformly, with an error smaller than \(y/\log z\) by a factor tending to zero. In particular all primes in the whole band have total log weight \(O(h)\), and flipping any subset of them has mismatch at most \(Ch^2\). This accounts for all the correction primes below, including those pre-installed before the free choices. [Guth and Maynard, Corollary 1.3](https://arxiv.org/pdf/2405.20552#page=2)

Write \(\Delta=\log n-s\). If \(dW=\sum_{q\mid n}q\log q-\sum_{q\mid P}q\log q\), the fact that \(P\) divides at exactly the primes \(q\le z\) gives \(T_z(n)=dW-z\Delta\). Therefore
\[
  D(n)-D(P)=(s-z)\Delta+\tfrac12\Delta^2-T_z(n).                        \tag{2}
\]
At a stopping point the linear term vanishes identically. For any other \(z\), (1) still proves the lower bound \(D(n)\ge D(P)-Ch^2-|s-z|z^{-A}\).

## Prime patterns giving small, positive log increments

For each half-integer \(a=j/2>0\) needed below, choose \(k=\lfloor a\rfloor+1\) and \(t=\lfloor z^{1-a/k}\rfloor\). Then \(0<1-a/k\le1/2\) and \(t^k/z^k\asymp_k z^{-a}\). Use a separate interval \(I\subset[z+h/2,z+h]\) of length \(L\asymp_A h\) for this \(a\). There are at least \(L/(\log z)^{C_k}\) disjoint sets of \(2^k\) distinct actual primes of the form
\[
    \big\{m+\epsilon_1d_1+\cdots+\epsilon_kd_k:\epsilon_i\in\{0,1\}\big\}
    \ \subset I, \qquad
    t/(\log z)^{C_k}\le d_i\le t .                                      \tag{3}
\]
The shifts are shared by all the sets constructed in this interval.

For the proof, start with the set \(B\) of primes in \(I\), of density \(\delta=|B|/L\gg1/\log z\). Divide \(I\) into at most \(2L/t\) blocks of span at most \(t\). If the block counts are \(b_i\), Cauchy–Schwarz gives \(\sum_i\binom{b_i}{2}\ge\delta^2Lt/8\) for sufficiently large \(z\). These pairs all have a positive integer difference at most \(t\). A single difference has at most \(2L\) representations. Removing differences less than \(\delta^2t/128\) and the \(O_k(1)\) differences between existing subset sums of the previously chosen shifts leaves at least \(\delta^2Lt/16\) pairs. Thus one allowed \(d\) gives \(|B\cap(B-d)|\ge\delta^2L/16\). Replace \(B\) by this intersection. Every retained base point extends its former pattern by its translate through \(d\), still entirely in the original prime interval. The excluded differences make the new subset sums distinct. Iterate \(k\) times. At each fixed stage the density is at least an inverse power of \(\log z\), and \(t\) grows as a fixed positive power of \(z\). The pair estimates and exclusions therefore apply at every stage. Two final translates can intersect only if their base difference is one of at most \(4^k\) differences of pattern positions. A greedy disjoint selection preserves at least a fixed \(k\)-dependent fraction. Enlarging \(C_k\) absorbs the fixed constants for large \(z\), proving (3).

There are two possible prime subsets on each pattern, the vertices of even or odd parity in \(\sum\epsilon_i\). Each has \(2^{k-1}\) vertices. Choose the one of smaller log mass as its initial state. Swapping to the other state increases log mass by exactly
\[
   \left|\sum_{\epsilon\in\{0,1\}^k}(-1)^{k-|\epsilon|}
                 \log(m+\epsilon\cdot d)\right|
     =(k-1)!\int_0^{d_1}\!\cdots\!\int_0^{d_k}
              (m+u_1+\cdots+u_k)^{-k}\,du_k\cdots du_1 .
\]
This follows from \(k\) uses of the fundamental theorem of calculus and the constant sign of the \(k\)th derivative of \(\log\). Every such swap increases log mass by an amount between \(z^{-a}/(\log z)^{C'_k}\) and \(C'_k z^{-a}\). The positive lower bound makes the correction terminate; the upper bound gives the precision at that stage.

## Free choices, balancing and exact location

1. Fix the finitely many stages \(a=1/2,1,3/2,\ldots,J/2\) with \(J/2>A\). Split the upper interval \([z+h/2,z+h]\) into this many fixed intervals and one additional interval, giving the latter a fixed fraction independent of \(A\). On each stage interval reserve \(\lceil z^{2/3}\rceil\) disjoint patterns from (3). There are enough once \(z\) is large because \(\kappa>2/3\). Pre-install the initial parity class in each pattern, exchanging each added upper prime against a distinct lower prime of \(P\) in \([z-h,z-h/2]\). The number of lower primes required is \(O_A(z^{2/3})=o(h/\log z)\).
2. In the remaining separate upper interval create \(K\ge c_2h/\log z\) disjoint pairs of a fresh upper prime and a fresh lower prime from the lower interval. Reserve a fixed fraction of the lower interval's primes for later deletions. For each of the \(2^K\) binary strings independently choose which of these \(K\) exchanges to make. All initial replacements and free exchanges are from below \(z\) to above \(z\), with log increment at most \(O(h/z)\) each. Their accumulated surplus obeys \(0\le\Delta\ll h^2/(z\log z)\). The constants in this bound can also be obtained from the total count of available primes in the full band.
3. Remove previously unused lower primes in a fixed order until the net \(\Delta\le0\). The overshoot is smaller than \(\log z\), since the last deleted prime was below \(z\). If the surplus was zero there are no deletions. This needs \(O(1+h^2/(z\log^2 z))=o(K)\) lower primes.
4. For each stage, use its never-before-switched patterns in a fixed order, advancing the total log mass toward \(s\) as long as the next increment does not take it above \(s\). Stop that stage when the next switch would exceed the target or when equality has been reached. The initial deficit is at most \(\log z\). Later stages begin with a deficit at most \(C z^{-(a-1/2)}\). By the lower bound on each available increment, at most \(O_A(z^{1/2}(\log z)^{C_A})\) switches are needed at any stage, strictly fewer than its reserve \(z^{2/3}\). The final deficit at that stage is at most \(C'_k z^{-a}\). The last deficit is less than \(z^{-A}\) for large \(z\).

The free pairs and all correction sets are disjoint. One recovers each free bit from the divisibility of the finished integer by its designated upper prime. Unique factorization therefore gives \(2^K\) distinct squarefree integers even though the greedy corrections depend on the bit string. Every changed prime is among those budgeted in (2). This proves (1).

## What further concentration follows by counting

There is an **unconditional movable-center** consequence. Fix \(0<\lambda<\log 2\). Divide the prescribed log window of length \(z^{-A}\) into \(\lceil e^{\lambda K}\rceil\) equal bins. One bin contains at least \(2^K/\lceil e^{\lambda K}\rceil\) distinct integers from (1). Its width is at most \(z^{-A}e^{-\lambda K}\), and its center lies in the original window. Its location can depend on the outputs. At a high stop all these integers retain positive score; the sign there uses the premise on \(V\). Placing this much shorter bin exactly against the primorial would require a further estimate. At zero width the only integer of log mass \(s\) is \(P\) itself. More generally the elementary count in \([Pe^{-w},P]\) is at most \(1+Pw\).

The neighboring-maximum inequalities constrain a different quantity. At a stopped peak \(P\) which dominates neighboring candidates, (2) gives \(T_z(n)\ge\Delta^2/2\) for each candidate it dominates. On the balanced family the right-hand side is at most \(z^{-2A}/2\). Negative troughs elsewhere do not remove any of the \(2^K\) integers explicitly constructed at the given high peak. Thus enforcing two-sided exchanges and any fixed polynomial precision in log mass preserves the exponent \((1+b)/2\) if such peaks exist. A source-specific upper on the height or frequency of the peaks remains necessary to deduce the \(3/4\) count saving. [Neighboring primorial conditions](PRIMORIAL_NEIGHBORS.md) · [Squarefree count criterion](SQUAREFREE_COST.md)
