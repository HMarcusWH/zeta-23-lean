# A fixed allowance for opposite node charges

**DERIVED on paper.** The source-only inequality (3a) in [Local polarity windows](LOCAL_POLARITY_WINDOWS.md) holds with the coefficient of the opposite charges replaced by **3**, uniformly across the desired exponents. The growing neighborhood radius still permits arbitrarily small exponents. This pays for a genuinely positive surplus on the complete source. Opposite charges of comparable size can still compensate it.

Use the notation of (3a). For each desired exponent choose the same all-pole positive measure with the same contour estimates. Include arbitrary many smoothing boxes for Fourier decay, with total width one. Convolve with the uniform probability on `[0,4]`, so the resulting probability density has supremum at most 1/4. Write its support as `[0,A]`. Now convolve with the **unnormalized** indicator of `[-A-2,2]`. The resulting positive function K has supremum at most one, equals one throughout `[-log(2),0]`, and has Lipschitz constant at most 1/4: its derivative is a difference of two translates of a nonnegative density bounded by 1/4. These extra convolutions preserve (3), with constants and a support bound fixed before X is chosen.

On a shell V let v=q/V in [1,2]. The true coefficient is V^(−1/2) times the nonnegative function v^(−1/2) K(log(U/V)−log v). Its supremum is at most one and its Lipschitz constant is at most 3/4. Recall V^(−1/2) ≤ d_V ≤ sqrt(2)V^(−1/2). All target roots therefore have minimum at least d_U/2, all roots have minimum at most d_V, and every increment between node minima at descendant depth j is at most (3/2)d_V 2^(−s−j), using the parent width. Empty nodes contribute zero. The fine levels cost X^o(1) by the same weighted Cauchy inequality as in (3a). Therefore

```text
[P − 3N]_+ ≤ 2 |(K * λ_y)(log U)| + X^o(1).
```

Here P and N are the exact original dyadic-rational quantities of (3a). The factor three is independent of the exponent tolerance. With a uniform smoothing box of width 4/κ, for any fixed κ in (0,1], the same argument gives 2+κ in place of 3. The squared weighted sum is O_ε(X^ε) over all eligible interior target levels by summing 2^(−k). A complete arithmetic bound on the matched charge is still missing.

**An explicit dependence of the support on the accuracy.** For a=1/2+η, 0<η≤1/8, put e=(2a−1)/(2−a)≥4η/3. Corollary 1 of Chourasiya and Simonič bounds the integrated zero-density cost by

```text
W_a ≤ π [ 8.185·6/e⁴ + 9.461 (D²+2D+2)/H + 167.8 (D+1)/H ],
H=3·10¹², D=log H.
```

The first term uses ∫₁∞ t^(−1−e)(log t)³dt=6/e⁴ and the second and third terms use the actual cutoff H. The exponent of log in the paper is at most 3, so the replacement is valid for t≥H. In particular W_a<50η^(−4). All omitted visual scales and constants in the support above are bounded by a fixed multiple of 1+W_a+1/κ. Thus at any fixed exponent tolerance a finite neighborhood suffices whose required radius in dyadic shells is O(η^(−4)+1/κ). Full-source closure would still require the actual signed parity cancellation *within* these neighborhoods. [Explicit density parameters](https://arxiv.org/html/2507.15184v2#S1) · [Verified finite ordinate range](https://arxiv.org/abs/2004.09765)
