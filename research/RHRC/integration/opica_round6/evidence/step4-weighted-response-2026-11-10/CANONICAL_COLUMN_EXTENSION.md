# Complete canonical source column: archimedean cost and input transport paid

10 November 2026. **DERIVED paper construction and estimates, not new Lean compilation or an arithmetic upper.** This extends the actual prime-column bridge to the complete canonical source, using its literal current pole, direct equation-(4.4) archimedean and prime definitions. No unspecified gamma multiplier or normalization change is introduced.

## 1. Recover the exact archimedean operator from the current entries

The current `Components.lean` defines

    rho(u)=exp(u/2)/(exp(u)−exp(−u)), u>0,
    c0=EulerGamma+log(4pi),
    2 wCorrection(L)=c0−log((exp L+1)/(exp L−1)).

The production arch entry uses `sourceEq44GammaL`, not the historical printed gamma with its extra correction. Define on compact sufficiently regular whole-line functions

    (A f)(t)=c0 f(t)
       + integral_0^infinity rho(u)
          [f(t−u)+f(t+u)−2exp(−u/2)f(t)]du.               (1)

This is a Bochner L2 integral on H2 inputs. Near zero its bracket is bounded in L2 by

    u²||f''||_2 + 2(1−exp(−u/2))||f||_2;

rho(u)=O(1/u), so the product is integrable. At infinity rho(u)=O(exp(−u/2)), and translation is an L2 isometry. Thus (1) is well defined with no separate divergent scalar integrals.

Here is a direct check that (1) has the exact current physical arch matrix. Extend the normalized modes e_n(t)=exp(2pi i n t/L)/sqrt(L) by zero outside [0,L]. The sum of the two shift matrix elements is exactly qBasis(n,m,u,L) for 0<=u<=L and zero for u>L. For these finite modes the Bochner integral still exists: their zero extensions have translation differences O(sqrt(u)) in L2 near zero, which suffice against rho(u)=O(1/u).

For n!=m, (1) gives

    integral_0^L rho(u) qBasis(n,m,u,L)du
       = (alphaL(m,L)−alphaL(n,L))/(n−m),                 (2)

exactly the canonical off-diagonal arch entry. For n=m it gives

    c0 − 2 integral_L^infinity exp(−u/2)rho(u)du
      + 2 integral_0^L [cos(2pi n u/L)−exp(−u/2)]rho(u)du
      − (2/L) integral_0^L u cos(2pi n u/L)rho(u)du.       (3)

The tail is exactly

    2 integral_L^infinity exp(−u/2)rho(u)du
      = log((exp L+1)/(exp L−1)),                        (4)

as follows by substituting y=exp(−u) into 2/(exp u−exp(−u)). Thus (3) equals `2 sourceEq44GammaL(n,L)−2 betaL(n,L)`. Values assigned to the regularized integrand at the single point u=0 do not change any integral.

Equations (2)–(4) prove the full finite matrix correspondence, not only equality of one self-pairing. This is the direct production convention in `SourceWeilMatrixReconciliation.lean` and `CanonicalSourceChannels.lean`; the frozen printed correction is not used.

## 2. A uniform source-fixed archimedean column bound

The preceding estimate gives explicit constants independent of aperture:

    B0=|c0|+2 integral_0^1 rho(u)(1−exp(−u/2))du
                + integral_1^infinity rho(u)(2+2exp(−u/2))du,
    B2=integral_0^1 u² rho(u)du.

Both are finite. For every compact H2 function,

    ||A f||_2 <= B0||f||_2+B2||f''||_2.                  (5)

The whole-line definition is translation invariant. For the literal source h and any center b,

    Ah(.-b)=(A h)(t-b),
    ||A[h(.-b)]||_2 <= C_arch,h
       :=B0||h||_2+B2||h''||_2.                          (6)

Restriction to [0,L] cannot increase this bound. The actual signed arch contribution is not declared positive or discarded; its entire column has been bounded independently by the fixed source's regularity.

## 3. Pole normalization and complete canonical column

The integral operator on [0,L] with kernel

    2cosh((t−s)/2)

has, in the same normalized modes, the exact matrix entry

    32L sinh(L/4)² (L²−16pi²mn)
       /[(L²+16pi²n²)(L²+16pi²m²)].                     (7)

This is the current `poleComponent`. The factor two in the kernel matters: cosh alone would produce half the current entry.

For f_L(t)=h(t−L/2), both actual half-pole moments vanish, so (7)'s operator annihilates f_L pointwise. The compact packet lies fully inside [0,L] when L>=2S, including its flat endpoints. There is no pole-boundary remainder.

Let P_L be the complete zero-extended symmetrized prime-power shift operator from `NATIVE_BRIDGE_RESEARCH.md`. Its finite matrix is the exact `canonicalPrimeMatrix`, and

    P_L f_L(t)=Z(|t−L/2|).

Define the physical canonical source action by its three literal source channels,

    H_L f = Pole_L f − (A f)|_[0,L] − P_L f.             (8)

The entry calculations above and the existing production matrix decomposition show that its full finite Fourier matrix is `canonicalSourceMatrix`. In particular its ordinary Fourier compression on a finite coefficient vector is the exact current canonical matrix action. This note constructs and identifies that continuum extension at paper level; it does not claim an already compiled Lean function for (8).

For the unchanged compact packet, the complete source column is now exactly

    H_L f_L(t)=−(A h)(t−L/2)−Z(|t−L/2|).                (9)

No archimedean sign, prime-power omission or ground-ray assumption has been introduced.

## 4. Weighted response differs only by a paid fixed constant

Set T=L/2 and Omega_L(t)=exp(−(T−|t−T|)/2). Its squared L2 norm is 2(1−exp(−T))<=2. The prime-column identity and the reverse triangle inequality give

    | integral_0^L Omega_L(t)|H_L f_L(t)|dt − 2 A_Z(T) |
       <= integral_0^L Omega_L(t)|(A h)(t−T)|dt
       <= sqrt(2) C_arch,h.                             (10)

This is a source-fixed O(1) difference. A cofinal every-positive-rate upper for the complete physical canonical column is therefore equivalent to the selected upper for A_Z, after changing constants and using L=2T. A zero-dependent rate must be converted with the same factor two in the aperture: exp(eta T)=exp((eta/2)L). No change of horizon is hidden.

The complete canonical source can thus be used directly in the chosen response route. The archimedean contribution is now quantitatively paid; it is not another unproved arithmetic slot.

## 5. The exact input correction also survives this full canonical operator

The paper construction in `INPUT_MOMENT_CORRECTION.md` gives an exact even native moment-slice input phi_L with

    ||f_L−phi_L||_2 <= C exp(−c L^(3/2)).

The same estimate holds for its second derivative after changing fixed constants. For the Fourier tail, apply the Gevrey/Parseval argument to h''; for the four reserved correction modes, each second derivative multiplies its coefficient by at most (6pi/L)². Hence, with e_L=f_L−phi_L,

    ||e_L||_2+||e_L''||_2 <= C' exp(−c' L^(3/2)).         (11)

Both profiles have endpoint value and first derivative zero. Their zero extensions are therefore H2: no boundary delta or derivative of delta enters the weak second derivative. M2 and M4 are additional exact constraints, not substitutes for this H2 check.

Their exact half-pole conditions imply Pole_L e_L=0. Combining (5), (11) and the complete prime bound ||P_L||<=4L exp(L/2) gives

    ||H_L f_L−H_L phi_L||_[0,L]
       <= C''(1+4L exp(L/2))exp(−c' L^(3/2)).             (12)

This is smaller than every fixed exp(−B L) eventually. The weighted-L1 difference costs at most sqrt(2) times (12). Consequently the complete canonical **input-side** coupling is paid at paper level, including its archimedean channel, genuine pole constraints, endpoint corrections and every prime power.

## 6. Exact remaining limit

Equations (9)–(12) retain the full physical output. A finite source matrix returns Q_K H_L phi_L, and native moment compression may project further. Neither operation is justified as preserving the weighted absolute column or its L2 norm. The discarded output remains an OPEN adapter, and A11 still needs an independent bound on the actual core action on the actual packet loading.

This note does not prove a response upper. It pays the archimedean column and the full canonical input approximation, making the remaining mathematical object exact. The decisive arithmetic amplitude estimate remains OPEN; no RH or Step4 closure follows from this supporting composition.

### Source evidence

- [Current density, pole and correction definitions](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/Components.lean), freshly fetched earlier in this round and reread.
- [Exact physical qBasis](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/Kernel.lean), freshly fetched this round.
- [Direct equation-(4.4) convention](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/SourceWeilMatrixReconciliation.lean), current pinned snapshot reread for `sourceEq44GammaL` and `sourceEq44ArchComponent`.
- [Production pole-minus-arch-minus-prime theorem](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/CanonicalSourceChannels.lean), freshly fetched this round.
- [Actual pole-kernel and compression interfaces](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/CanonicalPoleNeutralGeometry.lean), freshly fetched this round. Its self-energy theorem does not grant output-norm equality.
