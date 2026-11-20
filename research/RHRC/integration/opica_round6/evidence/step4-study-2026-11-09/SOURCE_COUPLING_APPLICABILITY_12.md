# Actual source coupling applied to the geometry probes

9 November 2026. Immutable source head `b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7`, tree `d0a6b1ad78523c23834eb01f57f4910a22e30d3b`. This is a read-only proof investigation. The accompanying receipt binds five complete current source reads. No repository change, compiler run or new formal closure is claimed.

**Result.** The native moment-residual inequality does apply to every even geometry eigenvector, and yields a new explicit lower bound relative to the actual odd spectral bottom. It does not pay that bottom. The actual leakage normal also has a quantitatively nonvanishing off-axis transform, now proved from its own coefficients. Neither result bounds the full signed arithmetic response independently. Step4 and RH remain OPEN.

## 1. Exact interfaces, not interchangeable ground vectors

`GroundArithmetic.lean` proves the complete discrepancy identity for every actual even pole-neutral input u:

    S(u) = ArchContinuumRow(u) − SignedPrimeDiscrepancy(u),
    SignedPrimeDiscrepancy(u)
      = −∫₀ᴸ e^(−y/2)[ψ(eʸ)−eʸ]
                   [correctedSourceTestDerivative(u,y)−correctedSourceTest(u,y)/2]dy.

All prime powers and the complete signed discrepancy remain. The stricter equations S(r)=1 and primePairing(r)=−1−archPairing(r) require the actual source-normalized even ground ray, at the strict inequality λ_even<λ_odd. They are not identities for arbitrary geometry vectors.

In the strict odd case the input with S(v)=−1 is the separately defined reciprocal **even** input. The odd source-normalized eigenray carries the absolute-energy identity. Identifying these two inputs would invalidate the arithmetic substitution.

`JointGroundConstraints.lean` exhausts the strict-even, strict-odd and tied cases. The tied case retains each singular kernel and the complete complementary response; it does not supply a uniform inverse through a zero spectral gap. Its cofinal theorem allows a common K supplied by the parity producer. It does not identify this K with the quartic detector/geometry cutoff.

These facts nevertheless interact with the geometry through the following trial-residual theorem, whose hypothesis is not an eigenvector hypothesis.

## 2. A genuine source-to-geometry residual adapter

Fix L>0 and K≥3. Work in the actual even pole-neutral boundary-flat Hilbert space F and its M4-zero subspace S. Let A_F be `poleNeutralEvenCompressedCanonical`; let λ_o be `poleNeutralOddRayleighBottom L K hL hK`. Let w be the unit normal to S in F, with its actual Riesz normalization; the nonzero normalization is paid by the four-node argument in Pass11. Thus F is the orthogonal direct sum S⊕span{w}.

Let P be orthogonal projection onto S and put

    H=P A_F|S,      z=P A_F w,      ell=P D0 w.

Take the complete physical orthonormal eigenbasis v_i of the actual geometry compression G=P D0|S, with distinct eigenvalues θ_i separated by at least g>0. Put h_i=⟨v_i,Hv_i⟩, a real number. Every v_i has norm1 and M4(v_i)=0.

The exact native rank-two commutator gives, off the diagonal,

    (θ_j−θ_i) H_ji = z_j conjugate(ell_i) − ell_j conjugate(z_i),

up to the immaterial overall sign determined by commutator order. The entry modulus and all following bounds are independent of that choice. Hence

    Σ_(j≠i)|H_ji|²
      ≤ (2/g²)(|ell_i|²||z||²+|z_i|²||ell||²)
      ≤ 4||ell||²||z||²/g².

Self-adjointness and the **complete** decomposition F=S⊕span{w} now give

    ||(A_F−h_i)v_i||²
       = |z_i|² + Σ_(j≠i)|H_ji|²
       ≤ (1+4||ell||²/g²)||z||².

The |z_i|² summand is the omitted-normal leakage and is retained. Since ||ell||≤||D0||=K²,

    ||(A_F−h_i)v_i|| ≤ (1+2K²/g)||z||.                 (1)

The current declaration

    Zeta23.CCM.poleNeutral_momentFour_zero_residual_lower

states, with the actual trial residual A_Fu−λu, that M4(u)=0 and λ<λ_o imply

    (λ_o−λ)||u||/(2K) ≤ ||A_Fu−λu||.                 (2)

Its complete proof was read. It follows from the corrected source intertwining, the exact M4 pairing, the physical index norm upper and the index norm lower. In particular it does not assume u is a source eigenvector, S(u)=0, or a normalized ground ray.

Apply (2) with λ=h_i when h_i<λ_o; when h_i≥λ_o the same resulting floor is immediate. Equation (1) therefore proves for every geometry diagonal

    h_i ≥ λ_o − 2K(1+2K²/g)||z||.                     (3)

The standard complete off-diagonal reconstruction bound then yields, for every u∈S,

    ⟨u,Hu⟩ ≥ [λ_o − C(K,g)||z||] ||u||²,
    C(K,g)=2K(1+2K²/g)+2K²/g.                         (4)

This is a new DERIVED paper composition, not a new Lean declaration. The already supplied paper gap g≥c_geo K^(−241) makes C(K,g) polynomial at K=ceil(L⁴). No sharper gap is needed to make this cost polynomial.

What (4) pays is a **relative** diagonal floor. The unknown λ_o remains the actual absolute odd bottom at the same L,K. It cannot be replaced by zero or by a polynomial floor without further proof. In particular a polynomial bound for z would make the even slice lie within a polynomial distance below λ_o; it would not independently bound λ_o. This is not a counterexample to a possible stronger actual-source implication, only the exact remaining term in this proved composition.

The same formula must not simply be copied to odd parity. The odd geometry ambient F additionally removes M3 from the full odd pole-neutral space. A residual in the latter space therefore has the full M3-normal component as well as the M5-normal component. The even theorem (2) is not an odd theorem with renamed indices, and the extra component cannot be discarded.

An exact ground incompatibility is also visible: a nonzero even geometry vector, having M4=0, cannot be an A_F eigenvector at any eigenvalue strictly below λ_o, because (2) would give a positive quantity bounded by zero. Thus the strict-even ground ray and an even geometry basis vector cannot be substituted for each other in precisely the branch where that shortcut would appear useful.

## 3. What the production moment jets actually add

`CanonicalSourceMomentJets.lean` proves for an arbitrary genuine production coefficient vector x, if all centered moments below r vanish,

    derivative_(2r+1) sourceAtomRealEnergy(x,0)
       = 2[−(2π)²]^r |M_r(x)|².                      (5)

This is exact production-source information, not a generic matrix identity. Applying it to the actual unit leakage normals is legitimate after the established physical/raw parity coordinate identification. If alpha is the norm of the actual raw-power Riesz vector, then |M4(w_even)|=alpha and |M5(w_odd)|=alpha. The fixed odd coordinate phase changes neither modulus. Consequently

    derivative_9 sourceAtomRealEnergy(w_even,0)
       = 2(2π)^8 alpha²,
    derivative_11 sourceAtomRealEnergy(w_odd,0)
       = −2(2π)^10 alpha².                            (6)

For even geometry vectors M4=0, the ninth jet vanishes. For odd geometry vectors M5=0, the eleventh jet vanishes. Further moments are not automatically zero. Equation (5) must retain its entire vanishing-prefix hypothesis whenever used at a higher order.

The Riesz normalization is polynomially bounded above and below, so these particular jets are independently controlled by fixed powers. They describe derivatives at the source endpoint. No theorem inspected here converts a finite endpoint-jet bound into the signed complete prime pairing or the norm of P_S A_Fw. In particular (6) is not an estimate of either SG source slot and does not assign a sign to the complete transformed channel.

## 4. Why the smooth original-source estimates do not silently become estimates for w

`SmoothForcing.lean` defines its source, local physical response and forcing only from a `Step123NativeOutput`. The proof uses that output's literal `originalTrial`, stored finite detector, own physical projection, predecessor cutoff, eta and approximation channel. Its pairing is exactly

    ⟨v,smoothSourceForcing(out)⟩
      = W(originalTrial,forcingTest(v))
          + eta·weilTest(originalTrial,forcingTest(v),0),

and also exactly archChannel−primeChannel+spectralShiftChannel. The complete signed prime channel survives. Its independent norm bound is finiteForcingBudget+sourceForcingErrorBudget; the main budget contains exp(L/2), not the desired polynomial source upper. The later uniform error absorption pays the approximation error, not this main arithmetic budget.

A geometry eigenvector or w has not been supplied with that output record or its source identity. This is more than a missing name: their literal zero-extended physical profiles are nonzero finite trigonometric polynomials. Such a profile cannot be globally C-infinity with compact support, since all endpoint derivatives vanishing would force the analytic trigonometric polynomial to be identically zero. The originalTrial used by SmoothForcing is globally smooth. In the actual leakage normal the finite regularity failure is explicit: its first unpaid endpoint moment is M4 in even parity or M5 in odd parity, and it is nonzero.

This does not prevent a carefully proved approximation or a separate construction for w. It prevents the unsupported literal identification with the originalTrial. Nor does it identify w with the special stored finite detector: that detector has a particular construction and a paid, source-defined approximation error which an arbitrary normal does not inherit. All required approximation, normalization and inverse-response costs would need their own compatible derivation.

The genuine completed-input estimates from the earlier reviewed N34/N37 construction similarly apply to the stated integer drive and completion. They do not establish a range/inverse bound for the full prime field, and no identification of that history vector with w or v_i was obtained here.

## 5. The actual moving normal does have a quantitative transfer law

The previous report's attribution of a seed transform to w was incorrect. The original hash-bound report is preserved; see `SG_NATIVE_SOURCE_RESPONSE_CORRECTION_12.md`.

There is now an independent calculation for the literal normal. In real parity coordinates let d_n=n², beta=L²/(16π²), q_even=(1,sqrt2,...), q_odd,n=sqrt2·n, p_n=q_n/(beta+d_n), and let P3 be the monic cubic orthogonal to 1,d,d² for weights mu_n=p_n². Then r_n=p_nP3(d_n), alpha²=Σmu_nP3(d_n)² and w=r/alpha. These are the actual moving coefficients, up to the fixed odd unit phase.

For z=s²/c², c=2π/L, put

    J(z)=Σ mu_nP3(d_n)/(d_n+z),
    H(z)=Σ mu_nP3(d_n)²/(d_n+z).

Orthogonality gives P3(−z)J(z)=H(z). With δ=Re(s)>0,

    Re[s H(z)] ≥ δ alpha²/(K²+|z|),
    |J(z)| ≥ (δ/|s|)alpha²/(K²+|z|)^4.                (7)

The first inequality uses the genuine positive masses mu_nP3(d_n)² and the pointwise positive-real identity, not an arithmetic estimate. The centered transform convention is W(s)=∫_(−L/2)^(L/2)e^(sx)w(x)dx. Direct finite integration gives

    W_even(s)= 2s sinh(sL/2)(beta−z)J(z)/(sqrt(L)alpha c²),
    W_odd(s)= −2 sinh(sL/2)(beta−z)J(z)/(sqrt(L)alpha c).

The complete proof and explicit all-late polynomial-loss lower bounds are in `ACTUAL_NORMAL_TRANSFORM_VISIBILITY_12.md`. This agent independently reviewed its entirety, including constants. Its only zero in Re(s)>0 is the prescribed pole-neutral point s=1/2. Thus an individual off-axis exponential cannot be hidden by a zero of this moving filter.

This statement is about the filter, not a lower bound on the complete source response. In a zero representation, P_S A_Fw still contains the full complementary zeros with multiplicities and phases, as well as the actual projection. A single nonzero transfer does not prove the response norm grows; no rightmost-zero, simplicity or complement-smallness hypothesis is introduced. The first unproved prospective transfer is: does an actual visible off-line zero force cofinal superpolynomial growth of this complete projected response, with all complementary contributions retained? Even such a lower would still need an independent incompatible upper to close the route.

## 6. Exact mathematical state after this pass

Existing formally established current interfaces: complete signed source decomposition; strict even and odd ground arithmetic on their distinct actual inputs; exhaustive tied-ground kernel/complement equations; native geometry displacement and leakage; exact production moment jets. The receipt distinguishes the directly registered current Round4 CI roots from the two inspected imported CCM source files whose declarations are not separately in the 1321-root table.

New DERIVED paper consequences: the even source-residual/geometry adapter (1)–(4), the actual-normal moment-jet specializations (6), and the independently reviewed moving-normal transform estimate (7) with explicit visibility rates. These do not require an unproved cancellation estimate.

Not obtained: an independent polynomial floor for λ_o, a polynomial signed geometry-diagonal floor, a polynomial norm upper for the complete mixed response, an all-positive-damping prime-field energy upper, or an RH theorem. The new adapter explains exactly where source coupling is usable and where the remaining absolute arithmetic term enters; it does not erase that term.
