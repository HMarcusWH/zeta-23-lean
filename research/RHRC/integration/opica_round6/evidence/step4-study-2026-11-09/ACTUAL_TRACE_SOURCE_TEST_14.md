# Pass 14 — the actual trace test, paid continuum, and an unavoidable signed prime discrepancy

9 November 2026. Immutable source: PR299 `b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7`. **DERIVED paper calculation from the actual source; not newly Lean-compiled. Step 4 and RH remain OPEN.** All prime powers and both removed-normal corrections are retained.

This pass computes the literal scalar in the current trace identity, not a substitute source. Its continuum and Archimedean terms have independent polynomial bounds. Its actual prime test has a quantitatively negative terminal lobe whose absolute prime mass grows exponentially. Thus estimating this particular scalar by absolute prime weights is impossible at polynomial scale; the complete signed discrepancy remains the unpaid arithmetic quantity.

## 1. The literal source row and the fixed trace input

Fix `L>=2`, `K=ceil(L^4)`, `N=2K+1`, and `beta=L^2/(16*pi^2)`. Use raw centered Fourier coefficients indexed by `n=-K,...,K`, with the inherited Euclidean norm. All vectors below are real and even. Write

    d_n=n^2,     q_n=1,     p_n=1/(beta+n^2).
    E = {u: <q,u>=<d q,u>=<p,u>=0}.

The positive scalar relating `p` to the exact native pole profile cancels in the corrected-row construction. Let `h` be `correctedSourceRow L K`. Its literal definition gives

    h in span{q,d q,p},
    M0(h)=0,     <p,h>=0,     M2(h)=1,                (1)

where `Mj(v)=sum_n n^j v_n`. Indeed the first term of the corrected row is the quadratic normal divided by its squared norm; the second is the projected pole normal with exactly the coefficient needed to cancel its pole pairing. That projected normal has zero zeroth and second moments. These facts prove (1), including the normalization `1` rather than an unspecified multiple.

Consequently `h` is the unique vector in this three-dimensional span satisfying (1), and the minimum-norm vector among all vectors satisfying those three linear constraints. A concrete admissible competitor has

    h*_0=beta/4,
    h*_(+/-1)=-(beta+1)/6,
    h*_(+/-2)=(beta+4)/24,
    h*_n=0 otherwise.

Direct substitution proves its three constraints. Thus

    ||h|| <= ||h*|| <= sum |h*_n| = 2(beta+1)/3.       (2)

Let `D:E -> O` be the actual centered-index equivalence between the full native pole-neutral carriers, `M=D*D`, and `r=P_E(d^2 q)`, the fourth-moment Riesz vector. The trace input is exactly

    u = D^-1 c3 = M^-1 r.                             (3)

This is geometry-selected and independent of the prime coefficients. It is not the even ground ray or the odd reciprocal input.

For an entirely explicit construction, choose real `a,b` by projecting the vector `n^3` off the two odd normals `n` and `n/(beta+n^2)`. Equivalently, solve the positive-definite two-by-two system

    sum_(n=1)^K 2n^2 [n^2-a-b/(beta+n^2)] = 0,
    sum_(n=1)^K 2n^2 [n^2-a-b/(beta+n^2)]/(beta+n^2) = 0.

Its Gram is positive definite because the two functions `1` and `1/(beta+n^2)` are linearly independent on `1,...,K`. Then

    u_(+/-n)=n^2-a-b/(beta+n^2)       (1<=n<=K),
    u_0=-2 sum_(n=1)^K u_n.                            (4)

The first system equation is `M2(u)=0`. Substituting `u_0` shows the pole equation equals `-2/beta` times the second system equation. Thus (4) lies in `E`, and multiplication by the centered index gives the literal projected cubic `c3`; it is exactly (3).

Put `m=M4(u)`. The paid inverse estimate and positive metric give

    m=<r,M^-1 r>>0,
    ||u||<=4||r||<=4K^4 sqrt(N),
    m>=||r||^2/K^2>=1/(16K^4).                        (5)

The last inequality uses the previously proved four-node geometry bound `||r||>=1/(4K)` for this actual raw/even physical Riesz vector. The upper `M<=K^2 I` follows directly from the centered-index norm. No estimate for a prime field enters (1)–(5).

## 2. Complete arithmetic kernel of the trace scalar

Define the actual mixed source test

    T(y)=correctedSourceTest L K u y
        =sum_(n,m=-K)^K h_n u_m qBasis(n,m,y,L).        (6)

Here the exact production atom is

    qBasis(n,n,y,L)=2(1-y/L) cos(2*pi*n*y/L),
    qBasis(n,m,y,L)=[sin(2*pi*n*y/L)-sin(2*pi*m*y/L)]/[pi(m-n)]

when `n!=m`. The input, left row, signs, source coordinate and full raw cutoff are unchanged. In particular `T(0)=T(L)=0`.

For a finite harmonic representation, let

    A_n=h_n u_n,
    B_n=-(h_n sum_(m!=n) u_m/(n-m)
           +u_n sum_(m!=n) h_m/(n-m))/pi.

Then exactly

    T(y)=2(1-y/L)[A_0+2 sum_(n=1)^K A_n cos(2*pi*n*y/L)]
          +2 sum_(n=1)^K B_n sin(2*pi*n*y/L).           (7)

This is a concrete finite test, including the complete diagonal. All its coefficients are fixed by `L,K` before summing over primes.

The current source gives the exact scalar identity

    tr A_o-tr A_e = S(u)
      = -Arch(h,u)-sum_(q=2)^floor(exp L) Lambda(q)/sqrt(q) T(log q),   (8)

where `Arch(h,u)=<h,canonicalArchMatrix L K u>`. No term in (8) has been dropped or assigned a sign by normalization.

## 3. The complete continuum and Archimedean reference are independently polynomial

Let `H=||h|| ||u||` and `D_L=N(2+4*pi*K)/L`. The proved source-atom norm bound gives

    |T(y)|<=2H,       0<=y<=L.

Differentiating the literal entries gives maximum derivative in source coordinate at most `2+4*pi*K`: for off-diagonal entries use `|n-m|>=1`, and for diagonal entries use the displayed derivative. Hence

    |T'(y)|<=D_L H,
    |T(y)|<=D_L H y                                  (9)

by the lower endpoint zero. These are deliberately coarse polynomial bounds.

The current pole/source bridge is entrywise

    canonicalPoleMatrix = integral_0^L 2 cosh(y/2) sourceMatrix(1-y/L) dy.

Since the actual input `u` is pole-neutral, this proves the complete signed cancellation

    integral_0^L [exp(y/2)+exp(-y/2)] T(y) dy=0.

Consequently

    C_L:=integral_0^L exp(y/2) T(y) dy
        =-integral_0^L exp(-y/2) T(y) dy,
    |C_L|<=4H.                                        (10)

This is the whole continuum, not an endpoint truncation or a new asymptotic premise.

The exact direct equation-(4.4) Archimedean entries imply, because `<h,u>=0`,

    Arch(h,u)=integral_0^L rho(y) T(y) dy,
    rho(y)=exp(y/2)/(exp y-exp(-y)).                    (11)

The index-independent diagonal terms cancel by that orthogonality. This uses the repaired canonical formula, not the historically misprinted correction. The apparent singularity at zero is integrable by (9).

For `0<y<=1`, `y rho(y)<=exp(1/2)/2<1`; for `y>=1`, `rho(y)<=2 exp(-y/2)`. Equations (9)–(11) therefore give

    |Arch(h,u)|<=(D_L+8)H,
    R_L:=-Arch(h,u)-C_L,
    |R_L|<=(D_L+12)H.                                 (12)

At the native cutoff, `beta+1<=2K`, `N<=3K`, so (2),(5) make this a polynomial in `L` (for example an absolute constant times `L^29` suffices). This is a bound for the paid reference in (8), not the complete arithmetic scalar.

## 4. The remaining signed discrepancy is explicit

The already proved finite Abel identity supplies

    S(u)=R_L + integral_0^L E_psi(exp y) exp(-y/2)
                              [T'(y)-T(y)/2] dy,      (13)
    E_psi(x)=psi(x)-x.

Every prime power and both endpoints are present. For example, the presently available absolute estimate is

    |S(u)| <= (D_L+12)H
      +(D_L+1)H integral_0^L |E_psi(exp y)| exp(-y/2) dy.   (14)

The classical unconditional effective PNT makes the last integral at most `C exp(L/2-c sqrt(L))` after changing fixed constants and including the bounded initial interval. It does not make it polynomial or smaller than every fixed exponential. A direct proof follows from the effective estimate for `pi(x)-li(x)` by finite partial summation and the elementary proper-prime-power bound. The external arithmetic input is stated explicitly below.

Thus the first unpaid estimate here is signed cancellation in the particular integral (13), beyond an absolute PNT-error envelope. The scalar is genuinely more concrete than an arbitrary resolvent input, but no present closure consumer accepts a bound on this single relative trace displacement alone. Even a polynomial bound on (13) would still need an independently proved connection to an absolute ground floor or complete native response. We do not equate it with PG, SG, SB, or RH.

## 5. A quantitative terminal sign for this actual test

The literal source-entry Taylor series, including its diagonal, is

    sourceEntry(omega,n,m)
      =2 sum_(j>=0) (-1)^j (2*pi)^(2j) omega^(2j+1)/(2j+1)!
             sum_(a=0)^(2j) n^(2j-a) m^a.             (15)

Finite parity and moment cancellation in (1),(4) kills `j=0,1,2`. At `j=3` only `M2(h) M4(u)=m` survives. Hence

    T(L-L omega)=-[2(2*pi)^6/7!] m omega^7 + R(omega). (16)

This is a statement about the literal trace test; its coefficient is nonzero and negative.

For a uniform rather than qualitative lobe, let `B=||h||_1 ||u||_1`. From (2),(5),

    B <= (8/3)(beta+1) K^4 N^(3/2) <=32 K^7.

If `2*pi*K*omega<=1`, the remaining absolutely convergent series gives

    |R(omega)|<=2B(2*pi*K)^8 omega^9
               <=64(2*pi)^8 K^15 omega^9.             (17)

Take the fixed, conservative width

    omega_0=1/(100000 K^10).

Using (5), `pi<4`, and (17), the remainder is less than half the leading magnitude throughout `0<omega<=omega_0`. In particular

    -T(L-L omega) >= (2*pi)^6/(80640 K^4) omega^7,
                    0<omega<=omega_0.                 (18)

Thus the terminal lobe has rigorously paid inverse-polynomial width. No floating computation or fitted asymptotic was used.

## 6. An absolute prime estimate cannot close even this one scalar test

Let `X=exp L`, and keep the actual primes in the complete source whose logarithms lie in

    [L-L omega_0, L-L omega_0/2].

The classical effective PNT implies, for every sufficiently large real `L`, that their count is at least `X omega_0/8`. Indeed the interval length is at least `X L omega_0/4`; its logarithmic-integral mass is at least the length divided by `L`, and the error `O(X exp(-c sqrt L))` is smaller than half that main term. The moving width is a fixed inverse power of `L`, so this application is uniform despite `K=ceil(L^4)`.

Each of these primes has weight at least `L/(2 sqrt X)`, and (18) gives a common lower bound for `-T(log p)`. Therefore there is an explicit absolute `c_*>0` such that, at every sufficiently late real aperture,

    sum_(q=2)^floor(exp L) Lambda(q)/sqrt(q) |T(log q)|
       >= c_* exp(L/2) L/K^84
       >= (c_*/2^84) exp(L/2) L^(-335).               (19)

For example one can take `c_*=(2*pi)^6/(80640*2^7*16*100000^8)` from the displayed inequalities. Prime powers outside this interval are retained in the left side and are nonnegative contributions to this absolute sum. The signed terminal prime block itself is negative by the same magnitude. We have not asserted that the *complete* signed prime sum has that sign or size.

There is also a source-only continuous version: the negative terminal contribution to `integral exp(y/2)T(y)dy` has the same exponential-over-polynomial lower magnitude. Yet its complete integral is bounded by (10). The other signed lobes must compensate it. So the actual test necessarily has substantial positive and negative weighted continuum parts; pole-neutrality does not make it pointwise harmless.

Equation (19) falsifies a polynomial bound obtained by absolute prime weights for this *particular geometry-selected trace input*. It does not falsify polynomial cancellation in (13), a bound on `S(u)`, or any actual Step 4 closing statement. Those signed possibilities remain open.

## 7. External input and qualification

Only Section 6 and the optional envelope after (14) use an external arithmetic theorem: the unconditional effective prime number theorem `pi(x)-li(x)=O(x exp(-c sqrt(log x)))` for some fixed `c>0`. NIST DLMF §27.12, equation (27.12.5), was checked directly: https://dlmf.nist.gov/27.12.E5 . No RH-dependent estimate from the adjacent equation (27.12.7) is used. All geometric, kernel, endpoint and continuum assertions preceding that application are finite algebra or elementary integration on the actual source.

Current proof interfaces read include SourceRow, SourceDiscrepancy, PrimeDiscrepancyIntegral, SourceMatrix, Kernel, Components, CanonicalSourceChannels, and the exact pole/source integral theorem in CanonicalPolePrimeDiscrepancy. Their reading scopes and hashes are recorded separately. No new compiler or CI authority is claimed for (1)–(19); the named existing Lean identities retain their existing authority.

**Result:** the actual fixed trace test is now explicit; its Archimedean/continuum reference is independently polynomial, and absolute prime control is rigorously too expensive. The complete signed Chebyshev pairing in (13), and the further bridge from this relative scalar to an absolute closing estimate, remain unproved.
