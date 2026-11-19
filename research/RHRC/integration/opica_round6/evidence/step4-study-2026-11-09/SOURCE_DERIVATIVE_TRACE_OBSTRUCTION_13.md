# Pass 13 — derivative geometry, trace, and the missing absolute ground

9 November 2026. Current source: PR299 at `b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7`, tree `d0a6b1ad78523c23834eb01f57f4910a22e30d3b`. **DERIVED paper calculation; no new compilation, repository change, or arithmetic upper. Step 4 and RH remain OPEN.**

The precise result of this pass is a limitation of a proposed composition: the actual derivative geometry, corrected rank-one relation, its trace and source–moment consequences, and the newly proved geometry-normal visibility do not by themselves supply an absolute native ground floor or an eigenvalue interlacing theorem. A finite comparison construction proves this while retaining the actual derivative map and moment vector. It is not a model of the genuine prime arithmetic.

## 1. Exact current carriers and normalization

Fix `L > 0` and `K >= 3`. Write

    E = poleNeutralEvenSubspace L K,
    O = poleNeutralOddSubspace L K,
    D = poleNeutralIndexLinearMap hL K : E -> O,
    c3 = poleNeutralCubicCompressionVector L K,
    A_e = poleNeutralEvenCompressedCanonical L K,
    A_o = poleNeutralOddCompressedCanonical L K,
    S = poleNeutralCorrectedCubicSource L K.

Both carriers have complex dimension `K - 2`, by `finrank_poleNeutralEvenSubspace` and `finrank_poleNeutralOddSubspace`. These are the full native pole-neutral carriers, not a smaller extra-moment SG slice. Their metrics are the inherited coefficient Euclidean metrics, equivalent to the normalized finite physical Fourier norm. `D` multiplies raw centered Fourier coefficients by their integer index. The physical derivative additionally has the factor `2*pi*i/L`; that factor is not silently absorbed into this calculation.

The current source proves that `D` is injective and surjective, so its polar decomposition is

    D = U T,       T = (D* D)^(1/2) > 0,

where `U:E -> O` is onto and unitary. We do not replace `D` itself by a unitary. The actual inverse bound is `||D^-1|| <= 2`.

Use inner products conjugate-linear in their first argument. Define the literal fourth-moment Riesz vector `r in E` by

    <r,u> = centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u).

The exact theorem `poleNeutral_cubic_pairing_eq_momentFour` says

    <c3,D u> = <r,u>,       hence D* c3 = r.             (1)

Consequently, if `g = U* c3`, then

    r = T g,       g = T^-1 r.                          (2)

No arbitrary proportionality or unpriced normalization is present in (1)–(2).

Current source anchors:

* `CanonicalPoleNeutralCarrier.lean:171,182`: the two exact dimensions.
* `CanonicalPoleNeutralGeometry.lean:132,139,146,163`: the actual map and its equivalence.
* `CanonicalPoleNeutralSourceMoment.lean:28`: the inverse bound.
* `CanonicalPoleNeutralNormals.lean:325`: exact cubic/fourth-moment pairing.

## 2. What the genuine trace identity actually gives

For the actual source the exact relation is

    A_o D - D A_e = c3 S,                               (3)

where the functional on the right is constructed, not freely supplied. In particular `CanonicalPoleNeutralNormals.lean` defines it as the cubic defect minus the exact removed-output normal coefficient times the pole quadratic normal coefficient. That correction remains part of the arithmetic object.

Let `M=D*D=T^2`. Equation (1) gives the useful exact re-expression

    D^-1 c3 = M^-1 r.

The already proved `native_even_trace_displacement` is therefore

    tr A_o - tr A_e = S(M^-1 r),
    ||M^-1 r|| <= 4 ||r||.                             (4)

This pays the inverse geometry in this particular trace test. It does not bound its signed source value. More explicitly,

    |tr A_o - tr A_e| <= 4 ||S|| ||r||                 (5)

is only useful after an independent bound for the actual `S` (or the single tested value in (4)). Such a bound has not been obtained here. Even a small relative trace difference would not, by itself, anchor the common absolute spectral level.

For an actual even eigenvector `A_e u=lambda u`, the proved source–moment relation remains

    Re(conj(S(u)) <r,u>)
      = Re <(A_o-lambda)D u,D u>
      >= (lambda_odd-lambda) ||D u||^2.                (6)

This compares the even eigenvalue with the actual odd bottom. The right-hand reference `lambda_odd` is not removed by (4). The pass-12 residual adapter likewise retains precisely this absolute odd bottom.

## 3. Comparison construction with the actual derivative geometry fixed

The following operators are deliberately denoted with a tilde. They are not asserted to equal the prime/Archimedean canonical operators. Their purpose is to test an argument using only (1), Hermitian symmetry, and the rank-one relation (3).

Define on the actual finite space `E`

    B = integral_0^infinity exp(-tT) g g* exp(-tT) dt.   (7)

The integral converges in operator norm because `T>0`. It is positive semidefinite and solves the exact Lyapunov equation

    T B + B T = g g*.                                  (8)

For `tau>0` and `epsilon in {+1,-1}`, put

    Atilde_e = epsilon tau B,
    Atilde_o = -epsilon tau U B U*,
    Stilde(u) = -epsilon tau <g,u>.                     (9)

Both operators are Hermitian. Direct substitution, retaining `D=UT`, gives

    Atilde_o D - D Atilde_e
      = -epsilon tau U(BT+TB)
      = c3 Stilde.                                    (10)

Thus the exact derivative relation holds with the actual `D`, `c3`, `r`, norms and carrier dimensions. This is stronger than choosing unrelated toy derivative matrices.

Its trace displacement is exactly

    tr Atilde_o - tr Atilde_e
      = -2 epsilon tau tr B
      = Stilde(D^-1 c3),                              (11)

because, in an orthonormal `T` eigenbasis,

    B_ij = g_i conjugate(g_j)/(t_i+t_j),
    2 tr B = <g,T^-1 g>.

All source–moment identities and their ground-gap inequalities obtained from (10) and Hermitian symmetry also hold, with `Stilde`. They are not contradicted when the spectra move apart: their source product grows by the corresponding factor.

## 4. Strict sign separation on the actual geometry

Here is a complete finite argument that `B` is positive definite for the actual even native geometry. It uses no prime estimate.

In the real orthonormal endpoint-rephased even coordinates, let `d_n=n^2`, `n=0,...,K`, `q=(1,sqrt(2),...,sqrt(2))`, `beta=L^2/(16*pi^2)`, and `p_n=q_n/(beta+d_n)`. The actual even carrier is

    E = span{p,d p,d^2 p}^perp.

This is the same space as imposing the pole functional, zeroth moment, and second moment, since `q=(beta+d)p`. The fourth-moment Riesz vector is

    r = P_E(d^2 q) = p P3(d),

where `P3` is the monic cubic orthogonal to degrees at most two for the positive discrete measure with weights `p_n^2`. Also

    M = D*D = P_E diag(d_n)|E.                         (12)

Indeed the raw centered-index map has squared norm `sum n^2 |u_n|^2`; polarization gives (12). The even Fourier rephasing and the fixed odd unit phase do not alter this identity.

Construct monic orthogonal polynomials `P0,...,PK` for this positive measure on `K+1` distinct nodes. The normalized vectors `p Pj`, `j=3,...,K`, form an orthonormal basis of `E`. In this basis (12) is a real symmetric tridiagonal matrix with every adjacent off-diagonal coefficient strictly positive: multiplication by `d` raises monic degree by one, and orthogonality eliminates all lower non-neighbor entries. Compression discards the `P2` term and nothing inside this tail.

An eigenvector with first coordinate zero must have its second coordinate zero by the first row, and then every coordinate zero by induction. Each eigenspace has dimension at most one because an eigenvector is determined by its first coordinate. Thus `M`, and hence `T`, has simple eigenvalues and `r` overlaps every eigenvector. So does `g=T^-1r`.

For any `u != 0`,

    <u,Bu> = integral_0^infinity |<g,exp(-tT)u>|^2 dt > 0.   (13)

For if the integral were zero, its continuous integrand would vanish identically. Distinct exponentials `exp(-t_i t)` are linearly independent (differentiate at zero and use the Vandermonde matrix), and every `g_i` is nonzero. This forces `u=0`, a contradiction.

It follows from (9) that one comparison spectrum is entirely strictly positive and the other entirely strictly negative. Taking `epsilon=+1` makes the odd bottom arbitrarily negative as `tau` grows, with the actual geometry fixed. Taking `epsilon=-1` reverses the signs. For `K>=4`, there are at least two eigenvalues per carrier, so ordinary alternating eigenvalue interlacing is also false for this retained subsystem.

A shorter check suffices just for strict negativity on the even SG slice. For `K>=4`, `r` is not an eigenvector of `M`: otherwise `(d-lambda)P3(d)-Q2(d)` would be a monic degree-four polynomial vanishing at all `K+1>=5` distinct nodes. Consequently `g` is not parallel to `r`. With `S4=r^perp in E` and `u=P_S4 g`, one has `u!=0` and `<g,u>=||u||^2`. The integrand in (13) is already positive at `t=0`. Thus choosing `epsilon=-1` produces an arbitrarily negative Rayleigh value on the exact even extra-moment SG slice. This is a falsifier of the proposed geometry-only deduction, not of the actual arithmetic SG premise.

## 5. The metric commutator and filter visibility are retained

For the comparison operators,

    [M,Atilde_e] = epsilon tau (r g* - g r*).           (14)

Its form vanishes when both inputs lie in `S4=r^perp`. Let `w=r/||r||`, `G=P_S4 M|S4`, `H=P_S4 Atilde_e|S4`, `ell=P_S4 M w`, and `z=P_S4 Atilde_e w`. Splitting the complete carrier as `E=S4 direct-sum span{w}` gives exactly

    [G,H] = z ell* - ell z*.                           (15)

This is the same rank-two reconstruction algebra on the even SG slice. No omitted normal term is discarded. In particular the geometry gap and the actual normal `w` remain unchanged as `tau` varies.

The all-late nonvanishing normal-transform and projected-mode estimates proved in pass 12 concern this fixed source-independent geometry. They therefore still hold. They do not restrict the arbitrary scale in (9). This isolates why individual mode visibility, even with its polynomial transfer loss paid, cannot be substituted for control of the complete arithmetic source or its absolute ground.

## 6. Exact scope of the falsification

Retained: actual native carriers and dimensions; inherited metrics; actual centered-index equivalence and its inverse bound; actual `c3` and fourth-moment Riesz vector; Hermitian symmetry; the corrected rank-one relation as an abstract equation; its trace, metric and source–moment consequences; exact even SG slice/normal/geometry and its reconstruction algebra; geometry-normal filter visibility.

Not imposed: the requirement that `Stilde` be the actual constructed corrected cubic source; the complete canonical prime and Archimedean matrix formulas; the signed arithmetic source decomposition; the full time-domain divisor/completion identities; source-specific corrected-input identities and reciprocal arithmetic realization; a hypothetical-zero producer for this comparison model; the entire uncompressed source commutator beyond the stated native compressed identities. We have not realized these comparison operators by an unchanged arithmetic source.

The native tied-ground theorem has an equality-of-bottoms hypothesis, which is false in (9). In the sign-separated examples, the premise that both actual parity bottoms are negative is also false. Thus the comparison construction does not purport to satisfy the entire `NativeJointGroundConstraints` record or refute its actual-source conclusion. If one shifts both comparison operators by the same scalar, (10)–(15) and their relative identities persist while the common absolute level changes; that elementary observation is consistent with, but is not the main result of, this pass.

The construction is consequently **not** a counterexample to RH, PG, SB, SG, or the source-specific ground constraints. It refutes only deriving an absolute floor/interlacing from the listed retained algebraic and geometric facts without using an additional genuine arithmetic restriction.

## 7. Historical inertia records newly read

Four previously unread archive contents were fully read, without execution: `inertia_audit.py`, `verify_inertia.py`, `results/inertia_summary.json`, and the byte-identical normal/optimized `inertia_verified_*.json` receipt. Their hashes and exact scope are in the accompanying archive reading receipt.

They count eigenvalues below the positive threshold `1/1024` at `L=2,3,13/4,7/2`. The reported even/odd counts are `3/3`, `16/15`, `22/21`, `29/28`. These are not counts of negative eigenvalues. The proposal stage uses floating eigendirections only to choose an integer congruence; the checker tests exact interval diagonal-dominance gaps for the full transformed matrix, conditional on its supplied analytic source enclosures. The two parities have different dimensions in this historical boundary-flat carrier, unlike the equal-dimensional current pole-neutral carriers above.

Those finite count differences do not prove uniform parity interlacing or an all-aperture native floor. No fresh certificate execution, current-head authority, or infinite-range claim is inferred. Imported checker routines and individual large certificates were not newly audited here.

## 8. Result for the closure investigation

The paid new deduction is the fixed-geometry obstruction (7)–(15), together with the explicit current trace test (4). It rules out an unpriced transition from derivative coupling plus normal visibility to an absolute ground estimate. The still-unpaid arithmetic is the complete actual corrected source/prime action, or another actual-source restriction that controls the common ground/complement. The pass-12 bound relative to `lambda_odd` remains valid and remains relative. No independent signed upper, complete-complement cancellation bound, or polynomial odd-ground floor was proved in this pass.
