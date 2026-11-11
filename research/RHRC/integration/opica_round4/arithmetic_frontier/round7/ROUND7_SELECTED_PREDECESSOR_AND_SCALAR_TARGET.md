# Round 7: the selected predecessor is trivial, the three open targets are one, and the weakest form of that one is a scalar

11 November 2026. Author: the build session of this branch (Claude Code on `research/madness`). **Paper derivations, model computations and
finite certificates. No repository edit, no new Lean compilation, no CI qualification. Not independently reviewed.
Step 4 and RH remain OPEN.**

> Repository edition. It differs from the Drive file (sha256
> `14071c2c3185db76d5b1228116ddfb865a4c28befc0a9a5f8041720c118de947`) only in the author attribution above and in two
> file titles in section 10, which are replaced by descriptions.

Baseline: [PR299](https://github.com/HMarcusWH/zeta-23-lean/pull/299), head
`b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7`, tree `d0a6b1ad78523c23834eb01f57f4910a22e30d3b` (re-fetched; unchanged).
Input: the Round 6 handover and package (zip sha256 `b757302f0e06dc38bb200498307fe7c457023335c226139efec91efb3e0ba6c2`),
all eight notes and reviews read in full, plus the centered weighted-response lower and the output-recovery note.

## 0. What this round establishes, in one table

| # | Statement | Status |
|---|---|---|
| 1 | On every boundary-flat native carrier the canonical energy is the sum over zeta zeros `(4/L) sum_rho sinh^2(z_rho L/2) R(z_rho) R#(z_rho)`. | **PROVED** in the repository (`zeta_W_boundaryFlatFiniteVector_eq_canonicalSourceQuadraticForm`); my closed form is DERIVED and agrees with the prime-side Arb matrices to 14-16 digits at cutoffs 3 and 4, apertures 2 to 12 (EXPERIMENTAL SIGNAL) |
| 2 | The two cutoff-3 pole-neutral boundary-flat vectors are explicit: their transforms are `(z^2-1/4)` over a fixed product. | DERIVED, checked to 40 digits |
| 3 | Under a hypothetical off-line zero with displacement `delta`, for every `beta < delta` there are arbitrarily late apertures at which the least-crossing selector stops at cutoff 3, so both predecessor spaces are `{0}`. | DERIVED |
| 4 | If that zero strictly dominates, the selected cutoff is at most 4 at **every** late aperture, so the predecessor has dimension at most 2. | DERIVED; illustrated in two model runs |
| 5 | On those packets inequality (P) is, up to a fixed additive constant, no stronger than Cauchy-Schwarz, and target (E) is the plain `L^2` growth bound for the complete field `Z`: a stronger statement than (U), not a weaker supplier. | DERIVED |
| 6 | Target (F) is the weighted-energy form of (U): its numerator tends to a fixed positive constant, so the "loading ratio" is the reciprocal of the unknown energy and nothing else. | DERIVED |
| 7 | Weakest sufficient target: one explicit scalar function `E_e(L)` (the energy of the cutoff-3 even vector). `sup Re(rho) - 1/2` equals the least exponential rate at which `E_e` is bounded below. Under RH, `0 < E_e(L) <= 12.94 / L^5`. | DERIVED |
| 7b | Explicit floor adapter: on every boundary-flat carrier `E >= -4.4e-58 K^6 L^{-5} e^{(theta_0 - 1/2)L}`. With only the trivial `theta_0 <= 1` this gives unconditional floors on the whole quartic carrier, above `-1` for every aperture up to about 86. | DERIVED from the Lean-proved identity, the published verification of zeros to height `3e12`, and a crude count; a finite-range statement |
| 8 | At `L=2` (K=16) and `L=3` (K=81) the bottom eigenvalue is positive **and simple** on each constrained space tested. | FINITE CERTIFICATE (ball-arithmetic inertia; script unreviewed) |
| 9 | Native real-root lemma: on any native carrier, a simple bottom eigenvalue in a parity sector forces all transform zeros `z` of the ground vector to satisfy `z^2` real. Unconditional, and equally true if RH fails. | DERIVED |
| 10 | The ground-state convergence route consumes canonical positivity; it does not supply it. | DERIVED (dependency analysis) |

Nothing here bounds the arithmetic quantity. The round removes two of the three "alternative" targets as independent
options and reduces the remaining one to its smallest form.

## 1. The native explicit formula in closed form

Notation. Aperture `L>0`, `w_n = 2 pi n / L`, physical modes `e_n(t) = L^{-1/2} e^{i w_n t}` on `[0,L]`. For a
coefficient vector `c` of degree `K` put

\[
R_c(z)=\sum_{|n|\le K}\frac{c_n}{z-iw_n},\qquad
R_c^{\#}(z)=\sum_{|n|\le K}\frac{\overline{c_n}}{z-iw_n},\qquad
F_c(z)=\int_0^L f_c(t)e^{-zt}dt=L^{-1/2}(1-e^{-zL})R_c(z).
\tag{1.1}
\]

Write `z_rho = rho - 1/2` for the nontrivial zeros, with multiplicity. The repository's proved identity
(`Zeta23/ExceptionalZero/BoundaryFlatFiniteWeil.lean`, line 62; `W` is the sum of `Wsummand` in `Zeta23/Defs.lean`) says
that for boundary-flat `c` the canonical quadratic form equals `sum_rho F_c(z_rho) conj(F_c(-conj z_rho))`. Inserting
(1.1), and using `(1-e^{-zL})(1-e^{zL}) = -4 sinh^2(zL/2)` and `conj R_c(-conj z) = -R_c^{#}(z)`:

\[
\boxed{\ \langle c,\mathsf E_{L,K}\,c\rangle=\frac4L\sum_\rho \sinh^2\!\Big(\frac{z_\rho L}{2}\Big)\,R_c(z_\rho)\,R_c^{\#}(z_\rho).\ }
\tag{1.2}
\]

For a zero on the line, `z = i gamma`, the summand is `(4/L) sin^2(gamma L/2) |sum_n c_n/(gamma - w_n)|^2 >= 0`. For an
off-line quadruple `{+-p, +-conj p}`, `p = delta + i gamma0`, of multiplicity `m`, and a real parity vector
(`R^# = R`), the contribution is

\[
\frac{16m}{L}\,\mathrm{Re}\big[\sinh^2(pL/2)\,R_c(p)^2\big],
\tag{1.3}
\]

which has size `(4m/L) e^{delta L}|R_c(p)|^2` and either sign.

In the parity-reduced coordinates of `native_source.py` (even: `x_0, x_a`, weights `1,2,2,..`; odd: `x_a`, weights `2`):

\[
\text{even: } R(z)=\frac{x_0}{z}+\sum_a\frac{2x_az}{z^2+w_a^2},\qquad
\text{odd: } R(z)=\sum_a\frac{2i\,x_aw_a}{z^2+w_a^2}.
\tag{1.4}
\]

**Numerical validation (EXPERIMENTAL SIGNAL).** `lowdeg_check.py` compares the Gram matrix of the repository's Arb
matrix `pole - arch - prime` on the pole-neutral boundary-flat spaces with (1.2) summed over the first 400 numerical
zeros. Even sector, cutoff 3 (one-dimensional space):

| L | primes up to | prime-side energy (Arb, radius < 1e-89) | zero sum (400 zeros) | relative difference |
|---|---|---|---|---|
| 2 | 7 | 1.923991889063626e-4 | 1.923991889063626e-4 | 8e-17 |
| 3 | 20 | 8.558612138289437e-7 | 8.558612138289433e-7 | 4e-16 |
| 5 | 148 | 5.070945344741753e-9 | 5.070945344741749e-9 | 7e-16 |
| 8 | 2980 | 9.309436808451213e-13 | 9.309436808450827e-13 | 4e-14 |
| 10 | 22026 | 1.105984091718716e-11 | 1.105984091718715e-11 | 4e-16 |
| 12 | 162754 | 9.032227168061844e-15 | 9.032227168061044e-15 | 9e-14 |

The odd sector and cutoff 4 (two-dimensional spaces) agree to between 9 and 13 digits, limited by the slower decay of
the truncated tail. Full tables: `lowdeg_K3.json`, `lowdeg_K3_large.json`, `lowdeg_K4.json`. This confirms the
normalisation of every channel, including the production archimedean convention. It is a check of an identity already
proved in Lean; it proves nothing new by itself.

## 2. The cutoff-3 vectors are explicit

At cutoff `K` the even pole-neutral boundary-flat space is cut out by `M0 = M2 = 0` and the even pole functional; the odd
one by `M1 = 0` and the odd pole functional. Write `zR(z) = P(z^2)/prod_{a<=K}(z^2+w_a^2)` in the even case. Then
`deg P <= K`, `M0 = 0` and `M2 = 0` each lower the degree by one, and pole-neutrality is `P(1/4) = 0` (because
`F(+-1/2) = 0` and `1 - e^{-L/2} != 0`). At `K=3` this leaves `P(u) = c (u - 1/4)`. The odd case is the same with
`R(z) = i P_o(z^2)/prod(z^2+w_a^2)`, `deg P_o <= K-1`. Hence, up to sign,

\[
R^{\rm e}_3(z)=c_e(L)\,\frac{z^2-\frac14}{z\prod_{a=1}^3(z^2+w_a^2)},\qquad
R^{\rm o}_3(z)=i\,c_o(L)\,\frac{z^2-\frac14}{\prod_{a=1}^3(z^2+w_a^2)},
\tag{2.1}
\]

with `c_e, c_o > 0` fixed by unit physical norm. As `L -> infinity` the even vector tends to `(-20,15,-6,1)/sqrt(924)`,
i.e. the profile `sin^6(pi t/L)`, and `c_e(L) ~ 4 (2 pi/L)^6 720/sqrt(924)`. Checked to 40 digits at `L = 2, 12, 300`
(`k3_closed_form.py`).

Define the two scalar functions `E_e(L), E_o(L)` as the canonical energies of these unit vectors. By (1.2):

\[
E_e(L)=\frac{4c_e^2}{L}\sum_\rho\sinh^2\!\Big(\frac{z_\rho L}2\Big)\frac{(z_\rho^2-\frac14)^2}{z_\rho^2\prod_{a\le3}(z_\rho^2+w_a^2)^2},
\tag{2.2}
\]

and if every zero is on the line,

\[
E_e(L)=\frac{8c_e^2}{L}\sum_{\gamma>0}\sin^2\!\Big(\frac{\gamma L}2\Big)\frac{(\gamma^2+\frac14)^2}{\gamma^2\prod_{a\le3}(\gamma^2-w_a^2)^2}\ >0 .
\tag{2.3}
\]

On the prime side `E_e(L) = -<u, A u> - 2 sum_{n <= e^L} Lambda(n) n^{-1/2} (u*u)(log n)`: the pole term is zero and the
`e^{L/2}` main term of the prime sum is exactly cancelled by pole-neutrality. It is a smoothed, pole-compensated
Chebyshev sum with an explicit weight.

**A bound valid for every boundary-flat vector of degree `K`.** Three integrations by parts (the vector and its first
two derivatives vanish at both ends) give `|F_c(i gamma)|^2 <= L w_K^6 |c|^2 / gamma^6`. Summing over on-line zeros,

\[
0\le \mathsf E^{\rm on}_{L,K}(c)\le 2(2\pi)^6 S_6\,\frac{K^6}{L^5}\,|c|^2,\qquad S_6=\sum_{\gamma>0}\gamma^{-6}=1.44174\times10^{-7},
\tag{2.4}
\]

so the constant is `0.017742 K^6/L^5`: `12.94/L^5` at `K=3`, `72.7/L^5` at `K=4`. If RH holds this is the whole energy.

## 3. Where the least-crossing selector stops under a hypothetical zero

The selector (`Zeta23/CCM/NativeDeepThresholdGround.lean`, lines 75-80): `Cross K := 3 <= K <= Kd and
poleNeutralGlobalRayleighBottom L K < -eta`, cutoff `= Nat.find`, with `D/3 < eta < D/2` and, in the generated packet,
`D = e^{beta L}`. The global bottom is the smaller of the two parity bottoms. The spaces are nested, so the bottoms are
non-increasing in `K`. At `K=3` each parity space is one-dimensional, so `bottom_3(L) = min(E_e(L), E_o(L))`. At `K=2`
both are `{0}` (the structure's field `first_predecessor_empty`).

Assume a zero `1/2 + p`, `p = delta + i gamma0`, `0 < delta <= 1/2`, multiplicity `m`. Fix `0 < beta < delta`.

**Proposition 3A (robust; no dominance assumption).** For every `C > 0` the set `{L : E_e(L) < -C e^{beta L}}` is
unbounded. Consequently there are arbitrarily late apertures with `bottom_3(L) < -D`; at each of them the cutoff-3
vector is a legal unit trial of depth `D` in every larger carrier, the least-crossing cutoff is `3`, and the two
predecessor spaces are `{0}`.

*Proof.* Suppose `h(L) = E_e(L) + C e^{beta L} >= 0` for all `L >= L_1`. By (2.2), `E_e(L) = sum_rho T_rho(L)` with
`T_rho(L) = (e^{z_rho L} - 2 + e^{-z_rho L}) g_rho(L)`, `g_rho(L) = c_e(L)^2 k_L(z_rho)/L`, and
`k_L(z) = (z^2-1/4)^2 / (z^2 prod(z^2+w_a^2)^2)`. For `L >= L_1`, `|k_L(z_rho)| <= C' |z_rho|^{-10}` uniformly, and
`c_e(L)` is analytic in `1/L` near `0` with `c_e(L) = kappa_0 L^{-6}(1 + O(L^{-2}))`, `kappa_0 != 0`. Each `g_rho`
therefore extends holomorphically to a sector `|arg L| < theta_0`, `|L| > L_1`, with `|g_rho(L)| <= C''|L|^{-13}|z_rho|^{-10}`.
Let `Lap(s) = int_{L_1}^infty E_e(L) e^{-sL} dL`, convergent for `Re s > 1/2`. Rotating the ray of integration inside
the sector continues each term `int e^{-(s - z_rho)L} g_rho(L) dL` to the plane slit along a ray from `z_rho`, with a
bound `O(|z_rho|^{-10})` locally uniform away from `z_rho`. Since `sum |z_rho|^{-10}` converges and no `z_rho` is real,
`Lap` continues holomorphically to a neighbourhood of the real half-line `s > 0`. So does
`Phi(s) = Lap(s) + C e^{-(s-beta)L_1}/(s-beta)`, except at `s = beta`. Landau's theorem for Laplace transforms of
non-negative functions then gives convergence of `int h e^{-sL}` for `Re s > beta`; hence `Lap` is holomorphic in that
half-plane. But near `s = p` (and `Re p = delta > beta`) `Lap(s) = m int_{L_1}^infty e^{-(s-p)L} g_p(L) dL +` a function
holomorphic at `p`, and since `g_p(L) = a_0 L^{-13}(1 + O(L^{-2}))` with `a_0 = kappa_0^2 (p^2-1/4)^2 p^{-14} != 0`, the
first term has the singular part `-(m a_0/12!) (s-p)^{12} log(s-p)`. Contradiction. The same argument applies to `E_o`.
The embedding claim holds because zero-padding preserves the three moment sums and the two pole functionals. ∎

*Scope of 3A.* At these apertures a packet exists because the cutoff-3 vector is itself a deep legal trial
(`exists_nativeDeepThresholdGround_of_given_trial` accepts any such trial). They belong to the family of all apertures
at which some trial is deep, and to the family of Round 6's paper detector, which fires at every late aperture. If one
insists on the apertures of the compiled production detector, which is only known to fire cofinally, then in the
general case I have not shown that the two cofinal sets meet; under the dominance hypothesis of 3B the question does
not arise. Without dominance, at the remaining late apertures I have nothing beyond Round 6's cubic ceiling. (The
explicit formula bounds the form on boundary-flat carriers by `e^{delta_* L}` times a polynomial, with `delta_*` the
supremum of displacements, instead of the trivial `e^{L/2}`; that should sharpen the ceiling's constant and give a
linear ceiling when the supremum is attained, but I have not derived this carefully and do not claim it.) In every
case nothing forces the selected cutoff to grow.

**Proposition 3B (dominant zero).** Suppose every zero outside the quadruple of `p` has `|Re z_rho| <= delta' < delta`.
Then for every `beta < delta` there is `L_0` such that `bottom_4(L) < -e^{beta L}/2` for all `L >= L_0`. Hence the
least-crossing cutoff is `3` or `4` at every late aperture, and the predecessor `V` has dimension `0` or `2`.

*Proof.* At `K=4` the even space is `{(z^2-1/4)(s + t z^2) / (z prod_{a<=4}(z^2+w_a^2)) : s, t real}`. So
`R_x(p) = A(p)(s + t p^2)` with `A(p) != 0`, and because `Im p^2 = 2 delta gamma0 != 0` the factor `s + t p^2` takes
every complex value. Choose `(s,t)` with `sinh^2(pL/2) R_x(p)^2` real and negative. Computing the partial-fraction
norms (`|x| = O(L^8)` for `(s,t)=(1,0)`, `O(L^6)` for `(0,1)`) gives, for the unit vector,
`(16m/L)|sinh^2(pL/2)||R_x(p)|^2 >= c(p) L^{-17} e^{delta L}` with `c(p) > 0`. The on-line part is at most `72.7/L^5`
by (2.4) and the other off-line zeros contribute `O(e^{delta' L})`. The odd sector is the same. ∎

At `K=3` there is no freedom: by (2.1), `E_e^{off}(L) ~ -(4m c_e^2/L) e^{delta L} |p^2-1/4|^2 |p|^{-14} cos(gamma0 L + phi_e)`
with `phi_e = 10 delta/gamma0 + O(gamma0^{-2})`, and the odd vector behaves the same way with `phi_o = 8 delta/gamma0`.
So cutoff 3 is selected when one of the two cosines is favourable, and cutoff 4 otherwise.

**Model illustration (not the zeta function).** `hyp_selector.py` forms `E_on + E_off`: the true on-line sum (400 zeros)
plus one added quadruple, and runs the Lean selector rule.

| Model | Apertures sampled | Selected cutoff |
|---|---|---|
| `p = 0.3 + 17.3 i`, `beta = 0.1` | 26 values in `[420, 755]` | 3 at 13 of them, 4 at 12, 6 at one (`L = 420`) |
| `p = 0.45 + 28 i`, `beta = 0.2` | 9 values in `[417, 514]` | 3 at 3 of them, 4 at 6 |

Earlier apertures show the transient: no crossing below the tested cutoff, or cutoffs 5 to 8, while
`e^{(delta-beta)L}` has not yet overcome the polynomial loss. From `L = 433` on in the first model, and at every
tabulated sample of the second, the cutoff is 3 or 4, so the predecessor has dimension 0 or 2.
Files: `hyp_selector_d03_g173.json`, `hyp_selector_d03_g173_late.json`, `hyp_selector_d045_g28.json`.

**Relation to Round 6.** Round 6 proved a cubic *upper* ceiling `k = O(L^3)` for the selected predecessor and left open
whether a small cutoff actually occurs. It does: the ceiling is a constant. This is the opposite of the large positive
predecessor that estimate (G) would need.

## 4. Consequence for (P) and target (E)

Keep the Round 6 notation: `f_b = h(. - b)`, `B = H_L + eta`, `P` the projection onto the predecessor `V`,
`e_b = |B(I-P)f_b|_2`, `T = L - 2c_0`, `calE_L = 2e_{c_0} + int_0^T e^{-(T-t)/2} e_{c_0+t} dt`.

**Proposition 4.** At an aperture where the selected cutoff is `3` (cofinally many by 3A): `P = 0`,
`e_b = |(H_L+eta) f_b|_2`, and, by the canonical column identity `H_L f_b(t) = -(A h)(t-b) - Z(|t-b|)`
(pole annihilation and the full prime pairing, valid for `S <= b <= L-S`),

\[
\|Z\|_{L^2[0,L-b]}-C_{A,h}-\eta n_h\ \le\ e_b\ \le\ \|Z\|_{L^2[0,L-b]}+\|Z\|_{L^2[0,b]}+C_{A,h}+\eta n_h .
\tag{4.1}
\]

Therefore `calE_L >= 2|Z|_{L^2[0,L-c_0]} - 2C_{A,h} - 2 eta n_h`, and with `eta < e^{beta L}/2`, `beta < nu`:

\[
\text{(E) at such an aperture}\iff \|Z\|_{L^2[0,L-c_0]}\le C\,e^{\nu(L-2c_0)}\quad(\text{constants changed}).
\tag{4.2}
\]

But from (4.2) the conclusion of (P) follows in one line, with no predecessor:
`|Z_2(t)| = |int Z(s) h(t-s) ds| <= n_h |Z|_{L^2[t-S,t+S]}`, hence `A_{Z_2}(T) <= 2 n_h |Z|_{L^2[0,L-c_0]}`, while the
right side of (P) is at least `4 n_h |Z|_{L^2[0,L-c_0]} - 2 n_h C_{A,h}`. So on these packets (P) is, up to a
source-fixed additive constant, no stronger than Cauchy-Schwarz, and (E) is the `L^2` form of the original target at
the longer horizon `L - c_0`. Under 3B the same holds at every late
aperture up to a rank-two correction: `P f_b = <u_e,f_b>u_e + <u_o,f_b>u_o` with coefficients `O(L^{-1/2})` (Round 6,
equation (14) of the loading note, with `k=3`), and Round 6's own lower bound (17) shows this correction cannot change
the exponential rate.

This answers the six items of the handover's section D:

1. *Residual and output in native definitions.* With `P = 0` the residual is the source translate and its output is
   the complete canonical column (4.1): every prime power, both parities, the arch term; the pole term is zero.
2. *Comparison with the source-defined core.* The predecessor contains none of it; the Round 5 core lives entirely in
   the complement. No factorisation through `V` exists to be proved.
3. *Canonical-column recovery.* The residual is the genuine source column, so the Round 2 adapter applies verbatim and
   returns Round 2's statement. Nothing new.
4. *Ground constraints.* The selected ground is the explicit vector (2.1); its only "constraint" is the scalar (2.2).
5. *Cubic ceiling.* Sharpened to a constant ceiling (Section 3). The retained complement is the whole space.
6. *(F).* Section 5.

**What this rules out, precisely.** Any argument that derives the response bound from (i) positivity of `H_L + eta` on
the selected predecessor and (ii) approximation of the source inside that predecessor. It does not rule out a direct
arithmetic bound for `|Z|_{L^2}`; that is the original problem, with no help from the selector.

**Dependency table.**

| Statement | Source and variables | Used | Paid | Status |
|---|---|---|---|---|
| (4.1) | fixed `h`, `S <= b <= L-S`, any `eta` | column identity (Round 1/6 `R4`), `P=0` | arch `C_{A,h}`, shift `eta n_h` | DERIVED |
| (4.2) | as above, `beta < nu` | (4.1) | constants | DERIVED |
| cutoff 3 cofinally | hypothetical `p`, `beta<delta` | (1.2) PROVED; (2.1); Landau | none | DERIVED |
| cutoff <= 4 always | dominance hypothesis | (1.2), (2.4), explicit `K=4` family | polynomial `L^{-17}` | DERIVED |

## 5. Target (F) is the weighted-energy form of (U)

`v_L` approximates `Z` on `[0,T]`, `T = L/2`, with `|Z - v_L|_2 <= e^{-3L/4}`, and `|N f|_{L^2[0,T]} <= 2 e^{T/2}|f|`.
Hence `|N v_L - U|_{L^2[0,T]} <= 2 e^{-T}`. The drive `U` is a fixed non-zero function in `L^2(0,infty)` (its first
pulse is `(log 2/sqrt 2) h(t - log 2)`), so

\[
\|Nv_L\|_{L^2[0,T]}^2=\|U\|_{L^2(0,\infty)}^2+o(1)=:c_U^2+o(1),\qquad 0<c_U<\infty .
\tag{5.1}
\]

The numerator of (F) is thus bounded above **and below** by fixed positive constants. So (F) with constant `c` holds at
`T` if and only if `int_0^T e^{-gamma(T-t)}|v_L|^2 dt <= (c_U^2+o(1)) c^{-1} e^{eta T}`, i.e. if and only if
`W_gamma(T) <= C e^{eta T}`. There is no room for a "source-dependent orthogonality" or "angle law": the ratio is the
reciprocal of the unknown weighted energy times a constant. (F) is (U) in its weighted `L^2` form. DERIVED.

## 6. The weakest sufficient target

**Theorem 6 (scalar criterion).** Let `theta = sup Re(rho)` over nontrivial zeros and `alpha_* = inf{alpha >= 0 :
exists C, E_e(L) >= -C e^{alpha L} for all L >= 2}`. Then `alpha_* = theta - 1/2`. In particular

\[
\mathrm{RH}\iff E_e(L)\ge0\ \text{for all large }L\iff \forall\varepsilon>0\ \exists C:\ E_e(L)\ge-Ce^{\varepsilon L},
\]

and under RH `0 < E_e(L) <= 12.94/L^5`. The same holds for `E_o`.

*Proof.* `alpha_* >= theta - 1/2` is the Landau argument of 3A. Conversely, if all zeros have `|Re z_rho| <= a`, the
on-line terms of (2.2) are non-negative and the others are at most `(4c_e^2/L) e^{aL} |k_L(z_rho)|`, summable. Strict
positivity under RH: the transform of the vector vanishes only at `+-1/2` and at lattice points. ∎

Consequences for the project's formal targets. The compiled consumers SB, PG and SE ask for floors on whole parity
moment slices at the quartic cutoff. Theorem 6 says the same conclusion follows from a floor on **one** explicit
sequence of numbers, each a finite smoothed prime sum. None of the operator structure (whole slices, quartic cutoff,
moment slices, selected ground, near-null core) is needed to *state* the closing premise, and by Sections 4 and 5 none
of it currently helps to *prove* it. Theorem 6 is a reformulation of the classical equivalence between RH and
square-root cancellation in a smoothed Chebyshev sum. It is not a proof of the bound.

Rate ladder in this normalisation: a zero-free half-plane `Re s > theta_0` is the floor `E_e(L) >= -C_eps e^{(theta_0 -
1/2 + eps)L}`. Classical knowledge gives only the trivial `1/2`. The externally claimed boundaries `7/8`,
`0.874957019420098947`, `0.8733819666133` would give `0.375`, `0.37496`, `0.37338`. They were inspected at
source-statement level by the handover; I did not compile or audit them.

**Proposition 6b (explicit floor adapter; the easy half, with constants).** Let `theta_0 = sup Re(rho)` and let `H_0`
be a height below which every zero is on the line. For every aperture `L`, every cutoff `K` and every boundary-flat
vector `c`,

\[
\mathsf E_{L,K}(c)\ \ge\ -\,2(2\pi)^6\,S_6(H_0)\,\frac{K^6}{L^5}\,e^{(\theta_0-\frac12)L}\,|c|^2,\qquad
S_6(H_0)=\sum_{\gamma>H_0}\gamma^{-6}.
\tag{6.1}
\]

*Proof.* In (1.2) the on-line terms are non-negative. For an off-line zero, three integrations by parts and
Cauchy-Schwarz give `|F_c(z)||F_c(-conj z)| <= |gamma|^{-6} |f'''|_2^2 sinh(|x|L)/|x| <= |gamma|^{-6} w_K^6 L
e^{|x|L}|c|^2` with `x = Re z`. Sum over the off-line zeros, all of which have `|gamma| > H_0`. ∎

With the published verification of RH up to `H_0 = 3 x 10^{12}` (Platt and Trudgian, 2021; external, not re-verified
here) and the Riemann-von Mangoldt count, `S_6(H_0) <= 3.6e-63`, so the constant is `4.4e-58`. Using only the trivial
`theta_0 <= 1`, and `K = ceil(L^4) <= 2L^4`:

| Aperture `L` | unconditional floor on the whole boundary-flat quartic carrier |
|---|---|
| 7 | `>= -1.1e-38` |
| 20 | `>= -3.2e-27` |
| 60 | `>= -1.8e-9` |
| 80 | `>= -9.5e-3` |
| up to about 86 | `>= -1` |

For the scalar: `-3.2e-55 L^{-5} e^{L/2} <= E_e(L) <= 12.94 L^{-5} + 3.2e-55 L^{-5} e^{L/2}` for every `L`,
unconditionally. Status: DERIVED from a Lean-proved identity, a published computation and a crude count; not compiled.
This is a finite-range statement. The floor degrades like `e^{L/2}` and says nothing about late apertures, which is
where the closing consumers (SB needs one fixed floor at cofinally many apertures) apply. It does show concretely what
an improved `theta_0` or `H_0` buys: the same inequality with `e^{(theta_0-1/2)L}` or a smaller `S_6(H_0)`.

## 7. Audit of my earlier numerics (handover section E, first part)

The earlier bundle used midpoint matrices and an approximate eigen-solver. `certify_bottom.py` replaces the two
claims that matter by rigorous ones, given that `native_source.py` returns enclosures:

* an upper bound: the Rayleigh quotient of one explicit constrained vector, in ball arithmetic;
* a lower bound and simplicity: the inertia of `G - mu N` from a ball `LDL^T` (all pivots certified non-zero), for
  `mu` just below the bottom and for `mu` between the first two eigenvalues.

`L = 2`, `K = 16`, 1500 bits (all six spaces certified: no eigenvalue below `mu_1`, exactly one below `mu_2`):

| Space | dim | certified bottom in `(mu_1, RQ]`, `mu_1 = (1-10^{-6}) x` approx | second eigenvalue (approx) |
|---|---|---|---|
| even full | 17 | `RQ = 1.3422670796441115e-26` | 1.02e-20 |
| even flat pole-neutral | 14 | `2.2346878388925085e-20` | 6.40e-15 |
| even moment slice | 13 | `1.7539710835564704e-19` | 7.25e-14 |
| odd full | 16 | `1.6285192017526082e-23` | 4.56e-18 |
| odd flat pole-neutral | 14 | `3.2471320128813145e-18` | 5.48e-13 |
| odd moment slice | 12 | `3.5084804607915833e-16` | 1.05e-10 |

`L = 3`, `K = 81`, 3000 bits (matrix build 494 s; all six spaces certified in the same sense):

| Space | dim | certified bottom in `(mu_1, RQ]` | second eigenvalue (approx) |
|---|---|---|---|
| even full | 82 | `RQ = 3.3354437819712486e-91` | 2.57e-83 |
| even flat pole-neutral | 79 | `2.3056691153620339e-83` | 3.79e-76 |
| even moment slice | 78 | `3.9077234956047370e-83` | 6.47e-76 |
| odd full | 81 | `4.0847451377425336e-87` | 1.08e-79 |
| odd flat pole-neutral | 79 | `4.7161048272648992e-80` | 5.82e-73 |
| odd moment slice | 77 | `1.3420802049444488e-79` | 1.89e-72 |

Corrections to the first bundle: its "odd boundary-flat" number at `L=2` (`2.76e-23`) imposed only `M1 = 0`; the Lean
pole-neutral odd space gives `3.25e-18`. Its `L=2` and `L=3` even values are reproduced to all printed digits. The zero-matching and prime-reweighting
numbers remain EXPERIMENTAL SIGNAL and are explained, not strengthened, by (1.2): the ground vector of a Gram form
`sum_gamma |F(i gamma)|^2` must make `F` small at the zeros, so its transform zeros sit near them.

What the certificates do **not** say: anything about another aperture, a uniform margin, the limiting form, or RH. A
certified positive bottom at `L = 2, 3` is implied by the verified location of the low zeros together with (1.2); it is
a check of the machinery.

**Lemma 7 (native real roots; unconditional).** Let `X` be any of the native spaces (full, boundary-flat,
pole-neutral, moment slice) in one parity sector, and suppose the bottom eigenvalue of the canonical form on `X` is
simple. Then every zero `z` of the numerator of `R` for the ground vector has `z^2` real.

*Proof.* Write `zR = P(z^2)/prod(z^2+w_a^2)` (even) or `R = iP(z^2)/prod` (odd). The constraints are: an upper bound
on `deg P`, and the real root `1/4`. If `P(u_0) = 0` with `u_0` not real, put `P~(u) = P(u)(u - conj u_0)/(u - u_0)`.
Same degree, same real roots, so the new vector lies in `X` (complexified). The factor `B(z) = (z^2 - conj u_0)/(z^2 -
u_0)` satisfies `B(z) conj(B(-conj z)) = 1`, so the correlation `f * f~` is unchanged; the form is a translation-invariant
functional of the correlation and the norm is its value at `0`. So `P~` is another minimiser, not proportional to `P`.
Contradiction with simplicity. ∎

With the certified simplicity above, the ground polynomials at `L = 2, 3` have only real roots, without any
root-finding. The lemma uses nothing about zeta: it holds verbatim for the model forms of Section 3, whose ground
energies are hugely negative. Real-rootedness of finite ground states therefore cannot distinguish RH from its failure.

## 8. The ground-state convergence lead (handover section E, second part)

**Candidate theorem (CT).** For a sequence `L_j -> infinity` with simple even bottoms, let `Theta_j(z) = 2 sinh(z L_j/2)
R_j(z)` be the transform of the ground vector, normalised at one point. If `Theta_j -> xi(1/2 + z)` locally uniformly on
the plane, then by Lemma 7 and Hurwitz every zero of `xi(1/2+z)` has `z^2` real; real `z != 0` is excluded because zeta
has no zeros in `(0,1)`; so RH, and then canonical positivity by the compiled equivalence. So (CT) plus simplicity is a
sufficient target with every adapter already in place.

**What is available.** Lemma 7 (new here, paper level). Certified simplicity at two small apertures. Numerical
agreement of low zeros.

**The missing comparison, and why it is not independent.** The natural proof of (CT) compares the ground vector with
an explicit near-radical vector `k_L` whose transform is a multiple of zeta (the prolate construction in the
literature): `|H_L k_L| <= eps_L |k_L|`. That makes `k_L` close to *an* eigenvector with eigenvalue near `0`. To call
it the *ground* vector one needs (a) no eigenvalue below about `-eps_L`, and (b) a gap above. Statement (a) is canonical
positivity up to `eps_L`: Step 4 itself, in a stronger form. In the model of Section 3 the near-radical vector still
exists, sits in the middle of the spectrum, and the true ground vector (energy `~ -e^{delta L}`) has real-rooted
transform by Lemma 7 but does not converge to `xi`. So any proof of (CT) must already exclude that model. The route
consumes the missing estimate and returns RH, which the estimate returns anyway through the existing consumer.

Information gain of pursuing it: none for Step 4, unless someone finds a proof of convergence that does not pass
through spectral isolation of the near-radical vector. I do not have one and I did not find one in the material.
Status: LEAD with its first unpaid line identified as Step 4.

## 9. Where the round leaves Step 4

**Strongest new restriction.** Under a hypothetical off-line zero the actual generated packets have selected cutoff 3
at arbitrarily late apertures, and cutoff at most 4 at every late aperture if the zero dominates. There the "retained
complement at the earlier crossing" is the whole space, or the whole space minus two explicit low-frequency vectors.

**The three open suppliers are one.** (U), (F), (E) are, respectively, the weighted `L^1`, weighted `L^2` and plain
`L^2` growth bounds for the same field `Z`. Each of them, at rate `eta`, excludes zeros with displacement above `eta`
and is implied by their absence; none is a weaker intermediate of another.

**First unsupported line, in its smallest form.** For every `eps > 0`: `E_e(L) >= -C_eps e^{eps L}` for all large `L`,
with `E_e` the explicit scalar (2.2); equivalently `|Z|_{L^2[0,T]} <= C_eta e^{eta T}`. Nothing proved inside the
project bounds this at any rate below the trivial `1/2`. The external zero-free half-planes, if imported and audited,
would give a fixed rate near `0.373`.

**Falsification checks done.** Formula against primes (Section 1). Closed forms (Section 2). Boundary cases: cutoff 2
empty, cutoff 3 one-dimensional per parity, multiplicity `m` carried through, apertures down to 2. Model selector with
two parameter sets. The model is source-blind: it has no Euler product, so it refutes only arguments that do not use
the divisor identities. It is not evidence about the actual zeta function.

**Next deductions, by information gain.**

1. *Record the consolidation.* Replace "three alternative sufficient tasks" by one target in the closure-targets
   documents, with (4.2), (5.1) and Theorem 6 as the reasons. Cheap, and it stops further rounds on (E) and (F).
2. *An unconditional rate.* Write the converse adapter "zero-free half-plane `theta_0` implies `E_e >= -C e^{(theta_0 -
   1/2 + eps)L}`" (it is the easy half of Theorem 6) and, if the external proofs survive a real compile and axiom
   audit, obtain the first native floor below the trivial rate. This is progress on the ladder, not closure.
3. *A formal scalar consumer.* Formalise Theorem 6's hard half (explicit formula with moving test vector plus Landau).
   It would make the compiled closing premise a statement about one sequence. It is a reformulation; do it only if a
   scalar target is wanted for future work.
4. *The arithmetic itself.* A proof must lower the rate `alpha` in `E_e(L) >= -C e^{alpha L}` to zero. The only
   mechanism I know of that has moved `alpha` below `1/2` is the external family bootstrap, and its fixed point is
   near `0.373`. I found no contraction in the native identities; the divisor identities reproduce the same simple
   pole at each order (Round 6), and positivity arguments cannot see the unstable mode (Section 4).

I am not offering a closing theorem. I do not have one.

## 10. Files (sha256 in `SUMMARY.json`)

`lowdeg_check.py`, `k3_closed_form.py`, `hyp_selector.py`, `certify_bottom.py`, `zeros.py`; outputs
`lowdeg_K3.json`, `lowdeg_K3_large.json`, `lowdeg_K4.json`, `hyp_selector_*.json`, `certified_L2_K16.json`,
`certified_L3_K81.json`, `zeros_400.json`. The certified files contain the ground vectors with enough digits to
reproduce the Rayleigh quotients. Numerical zeros are mpmath values, not certified enclosures.

The first experiment bundle (approximate numerics, with its own ledger and corrections) is in the same Drive folder:
the bundle archive (id `11b3wOxKvUzvcPQ93G0VR8Tn51VPut4zo`, sha256
`6241097d02b2983914c1169b00acc71d21bb48971f511d3beaa77b30abf5f34e`) and its export ledger
(id `1hIk50MrQYPHLwXCTrgS_qLCHN05JJMrr`).

Reading ledger for this round: Round 6 notes and reviews (8), inherited canonical-column note, centered
weighted-response lower (`66_...`), output recovery (Round 2), documents 103 and 104 dated after the handover: content
read. Proofs re-derived where used: two-translate identity, column identity, selector definition (Lean source read).
Compiler-validated in this round: nothing.
