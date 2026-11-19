# Exact even native input correction with a paid source-error budget

10 November 2026. **DERIVED paper adapter; no new Lean compilation or arithmetic amplitude bound.** This extends the ordinary Fourier-input estimate to the exact even native moment slice. Complete output recovery remains separate.

## 1. Freeze the actual coordinates, source and cutoff

Let L>=2, K=ceil(L^4), omega_n=2pi n/L, and

    e_n(t)=exp(i omega_n t)/sqrt(L), 0<=t<=L,
    f_L(t)=h(t−L/2),
    c_n=<e_n,f_L>.

These are the same unshifted physical modes whose complete symmetrized prime-shift matrix gives `qBasis` and `primeComponent`. Centered frequency indices n are not a shift of the time variable. Since h is real and even, c_(−n)=c_n is real. Its explicit phase is

    c_n = (−1)^n H(i omega_n)/sqrt(L),

where H is the bilateral transform of h. Thus the alternating sign is already in c_n and is not to be inserted a second time into the native moment constraints.

Equivalently, if one uses centered-time modes exp(i omega_n(t−L/2))/sqrt(L) with coefficients a_n, then c_n=(−1)^n a_n. In those coordinates the endpoint constraints have the factors (−1)^n. The construction below always acts on c_n. For centered cosine aggregates it therefore acts on v_j=(−1)^j times the corresponding centered aggregate, including the usual paired-mode normalization.

The current source definitions checked are:

- `BoundaryFlatCoefficients`: centered moments M0=M1=M2=0;
- `poleNeutralEvenSubspace`: even coefficient parity plus those boundary-flat conditions and `canonicalPoleEvenFunctional=0`;
- `evenMomentSlice`: kernel of the fourth physical centered moment on that actual carrier.

The freshly fetched `MomentSlices.lean` explicitly defines the fourth moment on the physical coefficient vector, not on a rescaled or primitive vector. `CanonicalPoleNeutralGeometry.lean` defines the actual pole functional. The exact even pole profile is a nonzero L-dependent scalar multiple of 1/(beta+n²), beta=L²/(16pi²). Odd pole neutrality follows from even parity. Therefore it is enough to preserve real even parity and impose

    sum_n c_n=0, sum_n n²c_n=0, sum_n n⁴c_n=0,
    sum_n c_n/(beta+n²)=0.                                (1)

## 2. Why the infinite source coefficients meet these conditions

The actual smooth packet is flat at t=0,L. Absolute Fourier derivative convergence gives

    sum_n n^j c_n=0, j=0,2,4.                             (2)

For the pole condition, integrate the Fourier series against exp(−t/2). Since n is integral,

    integral_0^L exp(−t/2)e_n(t)dt
       = (1−exp(−L/2))/(sqrt(L)(1/2−i omega_n)).

Even coefficient pairing cancels the imaginary part. Thus

    integral_0^L exp(−t/2)f_L(t)dt
      = (1−exp(−L/2))/(2sqrt(L))
           sum_n c_n/(1/4+omega_n²).                      (3)

The left side is exp(−L/4) integral exp(−u/2)h(u)du=0 by the genuine source's half-pole moment. The factors in (3) are nonzero and `1/4+omega_n²=(4pi²/L²)(beta+n²)`. This proves the fourth condition in (1). The same moment with exp(+t/2) is consistent, but is not counted as an independent condition on an even packet.

## 3. Quantitative derivative-tail budget

The fixed q has the current proved Gevrey2 estimate. Fixed differentiation and compact convolution yield, for every fixed j, constants C_j,A_j>0 such that

    ||(h^(j+1))^(m)||_2 <= C_j A_j^m(m!)²

for all m. Constants precede L,K,m. The Fourier-input proof therefore applies to f_L^(j+1):

    ||(I−Q_K) f_L^(j+1)||_2
      <= B_j exp(−b_j sqrt(K/L)).                         (4)

For j=0,2,4, Cauchy and Parseval give the explicit weighted coefficient-tail budget

    E_j := sum_(|n|>K) |n|^j |c_n|
       <= sqrt(2/K) (L/(2pi))^(j+1)
                   ||(I−Q_K)f_L^(j+1)||_2.                (5)

Indeed sum_(|n|>K)1/n²<=2/K, and the remaining factor is the Fourier derivative energy of order j+1. This pays the derivative loss in the endpoint constraints rather than inferring small moments from L2 error alone.

At K=ceil(L^4), all E_j are at most

    B(1+L)^3 exp(−b L^(3/2))                             (6)

for fixed B,b>0. The zeroth and second moments have smaller polynomial prefactors, but (6) suffices. The truncated pole residual has modulus at most beta^(−1) E_0. For L>=2, beta is bounded away from zero.

## 4. An explicit four-node correction

Reserve native modes 0,±1,±2,±3; they lie below K. Set d=(0,1,4,9). An even correction is represented by aggregated numbers v_j: use coefficient v_0 at mode0 and v_j/2 at both modes ±j for j>=1. Its physical norm squared is

    |v_0|²+(|v_1|²+|v_2|²+|v_3|²)/2.                     (7)

Its three moment changes are sum_j d_j^r v_j, r=0,1,2, and its pole change is sum_j v_j/(beta+d_j).

Let m_0,m_1,m_2 be the negatives of the current truncated moments M0,M2,M4. First use

    v_2=(m_2−m_1)/12,
    v_1=(4m_1−m_2)/3,
    v_0=m_0−5m_1/4+m_2/4,
    v_3=0.                                               (8)

Direct substitution gives moment changes m_0,m_1,m_2 exactly. The fixed linear map in (8) has a fixed norm independent of L.

Let p_res be the pole residual of the truncated vector after (8). Define

    b=(-1/36, 1/24, -1/60, 1/360),
    D_beta=beta(beta+1)(beta+4)(beta+9).

The barycentric partial-fraction identities are

    sum_j b_j d_j^r=0, r=0,1,2,
    sum_j b_j/(beta+d_j)=−1/D_beta.                       (9)

Now add the second correction

    w_j=p_res D_beta b_j.                                (10)

It changes the pole residual by −p_res and preserves all three moments. The sign in (10) is positive because the partial-fraction sum in (9) is negative. No division by an unproved determinant or spectral gap is involved; beta>0 makes every denominator nonzero.

Let phi_L be the finite profile with both corrections applied. It belongs exactly to the genuine even pole-neutral boundary-flat carrier and has M4=0; hence it is a paper-constructed element of `evenMomentSlice L K`. It has not been identified with a ground eigenvector, reciprocal input or the repository's specific detector.

## 5. Pay the complete input correction

The first correction has norm at most a fixed multiple of E_0+E_2+E_4. After it, the pole residual has modulus at most

    beta^(−1)[E_0+C(E_0+E_2+E_4)].                       (11)

The second correction therefore costs at most a fixed multiple of

    D_beta beta^(−1)[E_0+C(E_0+E_2+E_4)].                 (12)

Using the deliberately coarse D_beta=O((1+L)^8), beta^(−1)=O(1), and (6), both corrections together are bounded by

    C(1+L)^11 exp(−b L^(3/2)).                           (13)

The original L2 Fourier truncation error is smaller of the same type. Absorbing the fixed polynomial in a smaller positive exponential constant gives fixed C5,c5>0 such that

    ||f_L−phi_L||_2 <= C5 exp(−c5 L^(3/2))               (14)

at every sufficiently large L. All constants and the lower threshold depend only on the fixed genuine source and the fixed correction nodes, not on later L.

The complete prime-power operator satisfies ||P_L||<=4L exp(L/2), so

    ||P_L(f_L−phi_L)||_2
       <= 4C5 L exp(L/2−c5 L^(3/2)).                     (15)

Every fixed exp(−B L) eventually dominates this error. The weighted-L1 source-column error costs at most sqrt(2) times (15). The full arithmetic coupling and every prime power remain inside P_L; the estimate only pays a tiny change of input.

## 6. A literal source-specific rank-versus-loading check

The same argument also works at M(L)=ceil(L³ log L), L>=2, once L is sufficiently large. In (4) the exponent becomes a fixed positive multiple of L sqrt(log L), while every derivative and four-node correction cost remains polynomial in L. Consequently

    ||P_L(f_L−phi_(L,M))||_2
       <= polynomial(L) exp(L/2−c L sqrt(log L)),

which is still smaller than every fixed exp(−B L) eventually. The exact corrected input lies in a Fourier space of dimension 2M+1=O(L³ log L), and the four correction nodes do not enlarge that support.

This is the same order as A11's *allowed* near-null-core rank, while the full quartic carrier has order L4. It therefore supplies a source-specific reason that a vanishing dimension fraction alone cannot force this literal packet to have negligible loading: the packet itself is approximable to the required accuracy in that many dimensions. This does not identify the selected A11 core with the low-frequency carrier or prove any actual core-loading lower or upper.

## 7. Qualification and remaining interface

The source q Gevrey estimate and carrier definitions are existing current Lean statements. Their combination, the four-node correction and (14)–(15) are new paper deductions here, not compiled declarations. The existing `boundaryFlatProject` corrects only moments0,1,2; it is not falsely credited with the extra fourth-moment and pole correction.

The native compressed matrix returns a projection of P_L phi_L, while (15) retains the whole physical output. No estimate here bounds the complementary output or replaces its norm by the compressed norm. The current `inner_poleNeutralEvenCompressedCanonical_self` preserves self-energy only. Its statement explicitly does not preserve the output vector.

Thus the exact even input-membership cost is paid at paper level. The subsequent `CANONICAL_COLUMN_EXTENSION.md` also pays the complete direct-source archimedean column and the H2 input error, while the pole channel annihilates both exact inputs. The output-projection cost and, more fundamentally, the genuine source response amplitude remain OPEN. This is supporting progress, not a proof of the selected arithmetic upper or of RH.

### Source links

- [UniversalSincPhysicalBounds](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/UniversalSincPhysicalBounds.lean)
- [BoundaryFlatProjection](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/BoundaryFlatProjection.lean)
- [CanonicalPoleNeutralGeometry](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/CanonicalPoleNeutralGeometry.lean)
- [MomentSlices](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/OPICARound4/ArithmeticFrontier/MomentSlices.lean)

These current files were freshly fetched during this review and preserved under `native-bridge-source/`.
