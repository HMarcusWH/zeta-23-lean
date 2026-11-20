# What a contrary covariance sign would locate

For the fixed cutoff \(Y=10^7\), a single nonnegative complete covariance \(R_Y(n)\) at an integer \(n\ge 50000\) would locate a rightward zero in a **finite interval of ordinates**. The implication uses the actual one-copy field. No contrary sign has been observed. This is a paper deduction from the [fixed-cutoff estimate](FIXED_SIEVE_SIGN.md) and its [uniform diagonal lower bound](ALL_HORIZON_DIAGONAL.md).

For such a zero write \(g=|\Im\rho|\), \(m=\lfloor\sqrt{g}\rfloor\), and \(\delta_\rho=\Re\rho-1/2\). At least one would have to satisfy
\[
 g>3\cdot10^{12},\qquad
 n\delta_\rho>m/32-17\log(m+2)+\log(10^{35}/3000)
 >\sqrt{g}/33 .
\]
Using the external ceiling, the same zero must satisfy \(g<(12n)^2\). The bounds on displacement and height here concern **one and the same zero**.

Indeed the mean of \(E_Y\) on the window exceeds \(10^{72}\). A nonnegative signed covariance forces \(\sup |P|\ge10^{36}\) on that window. All critical and trivial zero terms together cost less than \(10^{31}\). The published finite verification excludes off-line contributions up to \(3\cdot10^{12}\). At subsequent ordinates use the source's absolute weight in each square-root-height bin. The sum in bin \(m\) is bounded by \(3000(m+2)^{15}e^{-m/32}\) before temporal growth. The estimate counts zeros with multiplicity and both signs of the ordinate. It comes from the one-copy sinc bound and zero count in the parent note. For leftward zeros the temporal factor is at most one. For rightward zeros it is at most \(e^{n\delta_\rho}\). If every rightward zero missed the first strict inequality above, the total for all off-line bins, including the leftward terms, would be at most \(10^{35}\sum_{m\ge\lfloor\sqrt{3\cdot10^{12}}\rfloor}(m+2)^{-2}<10^{35}\). Adding the critical and trivial terms would contradict the required supremum.

The function \(m/32-17\log(m+2)+\log(10^{35}/3000)-(m+1)/33\) is positive and increasing for \(m\ge1732050\). For the upper height bound, the fixed-cutoff estimate has already excluded a contrary sign through \(n=144000\). For \(n\ge144000\) the displayed lower bound at \(m=12n\) exceeds \(0.37335n\), and it increases with \(m\). The difference at \(m=12n\) increases with \(n\) on this range. The external all-moduli theorem gives \(\delta_\rho<0.37335\). Hence \(m<12n\), which gives the asserted strict upper bound on \(g\). The endpoint checks and rational ceiling comparison are included in [the scalar certificate](check_fixed_sieve.py).

The finite-height localization tells us what a sign failure on an actual arithmetic graph would certify. Applying a growing finite-height verification to one window at a time supplies no proof that the sign recurs at unbounded horizons. [Native source and explicit formula](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeExplicitFormula.lean) · [Platt–Trudgian](https://arxiv.org/abs/2004.09765) · [External all-moduli zero-free theorem, including its rational endpoint](https://github.com/GTimG/QuasiRiemannTracker/blob/42cf5415cfaa4205caaa25ab11160724606cdc33/submissions/2026-11-13-continuum-exact-contact/src/Candidate/Main.lean#L274-L290)
