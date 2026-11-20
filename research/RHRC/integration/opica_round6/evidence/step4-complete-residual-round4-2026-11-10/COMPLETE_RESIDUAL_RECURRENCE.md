# A complete rough-integer recurrence: the exact gain and the surviving zero obstruction

11 November 2026, continuation of the 10 November round. **DERIVED paper algebra and estimates, pending independent review; no new Lean compilation, CI qualification, signed closing upper, or RH claim.** This attacks the complete residual from round 3, not only its already controlled huge-prime sector.

The result is a closed source-preserving recurrence with an exactly zero terminal forcing for the frozen-age field, and a superexponentially small forcing for the unmodified full source. However its actual positive delay kernel has no absolute contraction at any rate below 1/2, and its characteristic factor retains all the hypothetical zeta zeros. Completing the prime/smooth-cofactor substitution returns the unknown with coefficient exactly one. This determines why this regrouping alone does not pay the remaining arithmetic bound.

## 1. Inputs and historical exclusions retained

The preceding Vaughan, prime-insertion and full smooth-cofactor audits were reread before this attempt. In particular:

- An individual partial Euler stage is not assumed small merely because the final completed drive is small.
- Every small-prime power in a positive completion factor is retained.
- A reciprocal generating identity is not applied to physical fields without its causal product cutoffs.
- A signed prime-insertion sum is not replaced by its negative squares.
- A generic contraction of a positive majorant is distinguished from a source-specific signed estimate.

The unchanged fields and convolution operators are

\[
Z(t)=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}h(t-\log n),
\qquad
U(t)=\sum_{n\ge2}\frac{\log n}{\sqrt n}h(t-\log n),
\]
\[
(N*f)(t)=\sum_{n\ge1}\frac1{\sqrt n}f(t-\log n),
\qquad
(M*f)(t)=\sum_{n\ge1}\frac{\mu(n)}{\sqrt n}f(t-\log n).
\]

All inputs are causal and every displayed time sum is locally finite. Both U and Z vanish before t0=log2-S>0. The literal identities N*Z=U and M*U=Z remain in force. The actual source has fixed C,c>0 with

\[
|U(s)|\le C(1+s)e^{s/2}\exp(-c e^{s/2})\quad(s\ge0).
\tag{1}
\]

At a common horizon T retain the preceding frozen cutoff

\[
Q_T=B^2(T+2)^2,\qquad cB\ge2,
\qquad U_Q(s)=\mathbf1_{0\le s<\log Q_T}U(s),
\qquad V_Q=M*U_Q.
\]

The already paid difference between V_Q and Z on the complete prefix has weighted-L1 cost at most C_h(1+T)^2 exp(-3T/2). The complete residual is defined exactly by

\[
V_Q=\mathcal R_Q+D_Q,\qquad
D_Q=G_Q-G_Q^c,\qquad
\mathcal R_Q=B_Q+G_Q^c.
\tag{2}
\]

Here G_Q is the exact huge-prime sector of round 3, B_Q its complete complementary products, and G_Q^c the explicit continuum comparison. Their causal extensions and all cutoff conventions are those specified in the preceding notes. No part of B_Q is dropped.

The unique huge-prime interpretation is asserted only on the proved common late half. At earlier times use the exact causal formulas G_Q=-sum_(r<=R) Lambda(r)/sqrt(r) K_h(t-log r), the specified causal continuum extension, and the definition mathcal R_Q=V_Q-D_Q. The recurrence retains these complete earlier values. It does not reinterpret them as a disjoint huge-prime sector outside the range where that classification was proved.

## 2. Strip small primes with a finite, source-preserving operator

For a real y>=2 let

\[
\mathcal P_y=\prod_{p\le y}p,\qquad
\theta(y)=\log\mathcal P_y,\qquad
T_p f(t)=p^{-1/2}f(t-\log p).
\]

Define the finite squarefree operator

\[
M_{\le y}=\prod_{p\le y}(I-T_p)
=\sum_{d\mid\mathcal P_y}\mu(d)d^{-1/2}S_{\log d},
\tag{3}
\]

and the positive rough-integer operator

\[
(N_{>y}*f)(t)=
\sum_{\substack{d\ge1\\P^-(d)>y}}d^{-1/2}f(t-\log d).
\tag{4}
\]

The term d=1 is included by convention. Every prime factor of a nonunit d in (4) exceeds y; **all multiplicities are allowed**. In particular (4) is not a squarefree sum.

The exact coefficient identity

\[
M_{\le y}*N=N_{>y}
\tag{5}
\]

follows because the coefficient of an integer d on the left is the sum of mu(a) over divisors a of both d and the primorial. This is one if d has no prime factor at most y, and zero otherwise. The time-domain identity is finite at each time, so no analytic continuation is needed for this step.

Applying (5) to the complete genuine coupling gives

\[
\boxed{N_{>y}*Z=M_{\le y}*U,\qquad
N_{>y}*V_Q=M_{\le y}*U_Q.}
\tag{6}
\]

The second equality preserves the age cutoff exactly. Each delayed U_Q term still tests its own original integer-drive age; no cutoff is applied after convolving in a different order.

## 3. A terminal homogeneous recurrence with all earlier histories retained

Choose, once at this common horizon,

\[
y=y_T=\left\lfloor\frac{T}{8\log(T+2)}\right\rfloor.
\tag{7}
\]

For sufficiently large T, y>=2. The elementary estimate

\[
\theta(y)\le y\log y\le T/8
\]

uses no PNT. Also log Q_T<=T/8 eventually, with its threshold fixed from B. Every term of M_{\le y}*U_Q has support ending no later than

\[
\theta(y)+\log Q_T\le T/4.
\]

Consequently on the entire common late half [T/2,T],

\[
\boxed{
V_Q(t)+
\sum_{\substack{d\ge2\\P^-(d)>y}}
d^{-1/2}V_Q(t-\log d)=0.}
\tag{8}
\]

All summands with t-log d<t0 vanish automatically. Thus this is a finite, exact, same-horizon recurrence. Its minimum nontrivial delay grows like log y, but it also retains the full earlier history, including the initially paid chronological region. A small weighted norm of that initial region cannot be inserted after this convolution without paying the convolution's amplification.

The unmodified source has an equally exact recurrence with independently tiny terminal forcing. Indeed, for t in [T/2,T] and d dividing the primorial,

\[
t-\log d\ge T/2-\theta(y)\ge3T/8.
\]

Equation (1) and the finite coefficient mass bound

\[
\sum_{d\mid\mathcal P_y}d^{-1/2}
=\prod_{p\le y}(1+p^{-1/2})\le2^y
\]

therefore give

\[
\boxed{
|(M_{\le y}*U)(t)|
\le C_h(1+T)e^{T/2+y\log2}
\exp[-c_h e^{3T/16}].}
\tag{9}
\]

This is smaller than every fixed exp(-A*T) eventually. It is an estimate for the **actual full integer drive**, with every squarefree finite-Euler term retained. No modified arbitrary forcing is substituted.

Thus the full large-delay echo equation (6) is not missing a cheap forcing estimate on the late half. Its difficulty is the signed response of its delay operator.

There is also a precise tradeoff in this support-based argument. Removing every prime up to y gives a minimum remaining delay about log y, but the finite filter has maximum delay theta(y). Since ordinary PNT gives theta(y) asymptotic to y, keeping this maximum delay O(T) permits only y=O(T), hence a minimum remaining delay O(log T). Taking y=exp(aT) to force a fixed-fraction time delay instead introduces filter memory of order exp(aT). The preceding small-forcing proof then no longer applies on the current prefix. This does not prove the longer filter's signed output is large; it identifies the extra cancellation estimate that would be needed rather than treating that filtering cost as free.

## 4. The complete residual equation and its unpriced source term

Insert the exact full decomposition (2) into (8). The residual satisfies

\[
\boxed{
\mathcal R_Q(t)+
\sum_{\substack{d\ge2\\P^-(d)>y}}d^{-1/2}
\mathcal R_Q(t-\log d)
=-(N_{>y}*D_Q)(t),\quad T/2\le t\le T.}
\tag{10}
\]

This is a complete recurrence for the desired residual. It retains its entire arithmetic complement, every rough cofactor and prime power, all earlier ages, and the full centered huge-prime source D_Q.

The right-hand side is not declared small. The previous source-family estimate for D_Q was a pointwise running-envelope estimate for that component; it did not price applying N_{>y} to it. The operator's positive coefficient mass is large below the critical rate, as calculated next. Bounding D_Q first and then calling this convolved source paid would lose precisely the amplification under investigation.

Equation (10) is not replaced by a homogeneous equation for the residual. The homogeneous relation (8) is for the complete V_Q only.

## 5. Exact finite-prefix gain of the proposed absolute recurrence

For a fixed nonnegative eta, define the causal running norm

\[
\|f\|_{\eta,T}=
\sup_{t_0\le t\le T}e^{-\eta t}|f(t)|,
\]

with f zero before t0. This is the space of all bounded causal functions on the finite prefix, not a restriction to smooth profiles or the genuine arithmetic source. Write sigma=1/2+eta and X_T=exp(T-t0). The nonunit rough-delay operator B_y=N_{>y}-I has **exact** norm in this space

\[
\boxed{
\|B_y\|_{\eta,T}
=\mathcal G_\eta(T,y):=
\sum_{\substack{2\le d\le X_T\\P^-(d)>y}}d^{-\sigma}.}
\tag{11}
\]

The upper follows directly from the running norm and the full causal cutoff. Equality follows with the positive test f(t)=exp(eta*t) on [t0,T]: at the single time T, every permitted term attains its bound. This test calculates the operator norm only; it is not claimed to be the genuine arithmetic source.

For every fixed 0<=eta<1/2, all primes in (X_T/2,X_T] eventually exceed y_T. Unconditional PNT therefore gives

\[
\boxed{
\mathcal G_\eta(T,y_T)
\ge c_\eta\,\frac{X_T^{1/2-\eta}}{\log X_T}.}
\tag{12}
\]

This diverges exponentially in T. The conclusion already follows from a genuine positive subset of the exact kernel, not an invented coefficient sequence or an extended noncausal sum.

At eta=1/2, the prime harmonic sum between y_T and X_T diverges, of order log log X_T-log log y_T. Thus its gain does not tend below one at the boundary either.

For eta>1/2, sigma>1 and every nonunit rough integer exceeds y. For the chosen integer y=y_T, the elementary bound

\[
\sum_{\substack{d\ge2\\P^-(d)>y}}d^{-\sigma}
\le\sum_{d>y}d^{-\sigma}
\le\frac{y^{1-\sigma}}{\sigma-1}
\tag{13}
\]

tends to zero. Hence this absolute rough-echo recurrence has a genuine contraction only on the wrong side of the rate 1/2 threshold. It cannot deliver the every-positive-rate supplier needed by Step 4.

This is a measured failure of a specific absolute-norm tactic, not a lower bound for the genuine signed response. The exact signed relation (8) is far stronger than its triangle inequality, but no additional estimate of that anti-alignment has been obtained.

## 6. Largest-prime decomposition with full smooth completions returns coefficient one

The same obstruction can be located exactly in a proposed prime/cofactor iteration. Put N=floor(X_T). On the whole prefix all relevant inverse prime factors are at most N. Define

\[
L_z=M_{\le z}*U_Q.
\]

Grouping the finite inverse product by its largest inserted prime gives

\[
\boxed{
V_Q=L_y-\sum_{y<p\le N}T_p L_{p^-}
\quad\hbox{on }[0,T].}
\tag{14}
\]

No remainder of smooth or Type II products has been omitted: this is the telescope of every factor I-T_p between y and N.

Now complete every partial stage using the same V_Q and all its positive prime-power cofactors. For an interval I of primes let

\[
E_I=\prod_{p\in I}(I-T_p)^{-1}.
\]

Each factor is its complete causal geometric series, and at any bounded time only finitely many products contribute. Then, on the same prefix,

\[
L_y=E_{(y,N]}*V_Q,\qquad
L_{p^-}=E_{[p,N]}*V_Q.
\tag{15}
\]

Substitution into (14) produces the exact kernel

\[
\boxed{
E_{(y,N]}-\sum_{y<p\le N}T_pE_{[p,N]}=I.}
\tag{16}
\]

There is a direct coefficient proof that retains all multiplicities and boundaries. A nonunit integer d composed of primes in (y,N] occurs positively in E_(y,N]. It occurs negatively exactly once: at p=P^-(d), because d/p then has every prime factor at least p. Its complete coefficient d^(-1/2) cancels. The unit coefficient is one. No other coefficients remain.

This proves that completing **all** partial stages by the original response does not create a strict return coefficient. It returns the same unknown with coefficient exactly one. If instead those terms are estimated separately, their exact aggregate positive mass on the prefix is

\[
(1+\mathcal G_\eta)+\mathcal G_\eta
=1+2\mathcal G_\eta,
\tag{17}
\]

so separate absolute estimates are worse, not a contraction. On the late half L_y is exactly zero and (14) reduces to (8), with the large nonunit gain already measured in (11)-(13).

Applying this complete substitution to V_Q=mathcal R_Q+D_Q likewise returns mathcal R_Q with coefficient one and cancels the extra D_Q return algebraically. No fresh inequality appears. Any proposed smaller coefficient must identify an additional source-specific signed estimate, rather than suppress an uncompleted cofactor stage.

## 7. Hypothetical zeros survive the full characteristic factor, with every jet

On the initial convergent half-plane the rough-integer operator has transform

\[
\widehat N_{>y}(z)=
\zeta(z+1/2)\prod_{p\le y}(1-p^{-(z+1/2)}).
\tag{18}
\]

For an actual hypothetical off-line zero rho with Re rho>1/2 and p0=rho-1/2, every factor in the finite product is nonzero at p0, because its exponential modulus is less than one. Thus (18) has exactly the same zero multiplicity at p0 as zeta has at rho.

The forcing transform is

\[
\widehat{M_{\le y}*U_Q}(z)=
\left[\prod_{p\le y}(1-p^{-(z+1/2)})\right]\widehat U_Q(z).
\]

Dividing by (18) cancels the finite product exactly and returns

\[
\widehat V_Q(z)=\frac{\widehat U_Q(z)}{\zeta(z+1/2)}.
\tag{19}
\]

The frozen-age lower-jet errors and its surviving visible simple-pole response channel are therefore precisely those already audited in SHORT_FACTOR_ZERO_CHANNEL.md. The hypothetical zeta zero may have arbitrary multiplicity; the visible log-derivative response has a simple pole. A compact or tiny late forcing is compatible with that unstable inverse; the new recurrence does not remove it.

This test is valid at every finite horizon with y_T frozen. It does not interchange an infinite prime product at a zero. The finite Euler factors in the largest-prime identity (16) are also analytic at p0, and their exact identity is one. Differentiating it to any fixed finite order preserves every pole-jet contribution in a composed response. Thus neither multiple-zero jets nor a hidden derivative loss supplies an uncharged contraction.

For the residual equation (10), the source N_{>y}*D_Q remains, while the leading pole channel of mathcal R_Q can be annihilated by the zero of (18). This explains why the exact recurrence is consistent with the round-3 finding that the complete residual retains the leading hypothetical response. It is not a statement that such a zero exists or that its isolated channel dominates the actual field.

## 8. What this changes in the next mathematical action

The complete recurrence is now explicit and its easy forcing is paid. The exact unit return and the critical absolute-gain threshold rule out obtaining the missing upper merely by reorganizing all remaining products into prime insertions and then completing each stage with smooth cofactors.

The remaining new information must enter through a genuine signed estimate for the actual rough-history anti-alignment in (10), or an independent bound for the complete residual/native source column from another OPICA restriction. A numerical core count, a positive delay kernel, a large minimum delay, a compact forcing, or a smaller selected huge-prime component does not supply it.

No independent complete-source upper was obtained in this pass. The valid gain is an exact, all-complement recurrence and a precise diagnosis: its absolute contraction threshold remains eta=1/2, its finite-factor return coefficient is one, and its characteristic zeros remain the original ones.

### Sources and qualification

- [ActualSourceHyperbola.lean at current b3afa611](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/OPICARound4/ActualSourceHyperbola.lean): unchanged literal source and field.
- [NativeCompletionEquation.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/NativeCompletionEquation.lean): retained completion interface; no generic inverse bound inferred.
- The exact integer divisor identity and Gevrey localization are established at the preceding paper level in DIVISOR_RESEARCH.md and RECENT_INVERSE_ATTEMPT.md, with their current formal-source qualifications.
- Round-3 definitions, cutoff proof, and local multiplicity review: SHORT_FACTOR_SIGNED_ATTEMPT.md, SHORT_FACTOR_ZERO_CHANNEL.md and their independent review receipts.
- Historical exclusions: PASS16_PRIMITIVE_AND_SIGNED_PRIME_ENERGY_REVIEW.md, PASS18_CENTERED_JETS_AND_COMPLETE_COVARIANCE_REVIEW.md, and the full smooth-cofactor report inspected in the preceding round.
- The prime-count lower needed in (12), and the harmonic-prime consequence at its boundary, use ordinary unconditional PNT; a primary stronger source already inspected is [Fiori--Kadiri--Swidinsky, arXiv:2206.12557v2](https://arxiv.org/abs/2206.12557v2). No RH estimate is used.

All new work is paper-level. No source files, repository commits, or proof-validation gates were changed. Step 4 and RH remain OPEN.
