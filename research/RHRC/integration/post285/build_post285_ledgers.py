"""Write the post-285 (Steps 108-120, packages M70-M77) research ledgers.

Single source of truth for the post-285 status tables.  Run with `--write` to
regenerate the JSON ledgers in this directory and `--check` to verify they are
current.  Statuses here are reporting labels; theorem authority comes only from
the Lean modules named in PROOF_ROOTS.json and their CI receipts.

Ledgers written:
* PROOF_ROOTS.json          new Lean roots of this PR (PROVED_PENDING_CI until
                            the exact PR head passes the post-284 Lean jobs);
* OPEN_OBLIGATIONS.json     M70-M77 obligations plus cross-references to the
                            post-284 ledger rows they touch (that ledger is not
                            edited here; its #285 promotion belongs to the
                            separate #285 cleanup PR);
* STEP_STATUS_MATRIX.json   Steps 18-120, one row per step;
* WORKFLOW_HARVEST.json     PR #285 exact-head check runs;
* EXPERIMENT_DISPOSITIONS.json  post-285 falsifier dispositions.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
TERMINAL = "RH_OPEN"

MODULES = {
    "Zeta23/CCM/CanonicalSecularResolvent.lean": ("M74", "Steps 111-112, 116-118",
        "actual-canonical secular resolvent ray, determinant, Ward identity, contact phase lock"),
    "Zeta23/CCM/CanonicalSourceExcursion.lean": ("M70", "Step 108",
        "strict positive and negative source excursions for nonzero zero-sum z"),
    "Zeta23/CCM/CanonicalCenteredIndexPoincare.lean": ("M73", "Step 115",
        "centered-index Poincare constant 1/4 and contact-gap corollary"),
    "Zeta23/CCM/CanonicalSourcePrimeSampling.lean": ("M75", "Steps 119-120",
        "source Lipschitz bound, uniform negative window, opposite-signed individual prime summands"),
    "Zeta23/CCM/CanonicalSourceSpectralFlow.lean": ("M72", "Step 110",
        "first degenerate source passage on (1/2,1) for any carrier with a half-aperture negative vector"),
    "Zeta23/CCM/CanonicalShiftedSecular.lean": ("M26-M28/M14", "Steps 58-60, 64; branch analysis",
        "canonical shifted secular equation, simple even roots below the odd floor, contact overlap identity, odd-first and tied branch algebra"),
    "Zeta23/CCM/CanonicalContactOverlapSign.lean": ("M28", "Step 60",
        "sign of the contact resolvent overlap when A_L is positive semidefinite and B_L positive definite"),
    "Zeta23/CCM/CanonicalPrimeFreeF04.lean": ("M65", "Steps 21, 24, 27, 93, 101, 103, 105",
        "prime-free F04 derivative authority on 0 < L < log 2: first variation, Euler-corrected fixed second variation, mixed aperture derivative"),
    "Zeta23/CCM/CanonicalGlobalF04.lean": ("M65/F04", "Steps 21, 24, 27, 93, 101, 105",
        "F04 derivative authority at every L > 0: prime staircase as logarithmic indicators, seams glued by e(0) = e'(0) = e''(0) = 0"),
    "Zeta23/CCM/CanonicalLocalBirdfishie.lean": ("M66", "Steps 74, 102-104",
        "prime-free Euler curvature bound, stationary second value = 2<Aw,w>, no stationary generated strict-even contact below eps_K, unconditional F04 frontier"),
    "Zeta23/CCM/CanonicalWeightedChebyshevAbel.lean": ("M55/M38", "Steps 75, 96",
        "exact weighted Chebyshev partial summation psi(x) - x = 1 + sqrt(x) R(x) - (1/2) int_1^x R/sqrt t, transfer bound, exact finite sup and inf of R on [1, X]"),
    "Zeta23/CCM/CanonicalSecularGronwall.lean": ("M31", "Step 66",
        "abstract Gronwall lower bound; canonical even-bottom barrier CONDITIONAL on the OPEN Gronwall inequality (67.1)"),
    "Zeta23/CCM/CanonicalAndreiefInertia.lean": ("M71", "Steps 44, 109",
        "exact even/odd boundary-flat source inertia for every 0 < omega <= 1/2: Andreief identity, signed leading minors, Jacobi split by Cramer vectors, carrier Gram as an Andreief convolution"),
    "Zeta23/CCM/CanonicalAlternatingRootSlopes.lean": ("M27", "Step 59",
        "1 - T_L(lambda) = prod(a_i - lambda)/prod(b_k - lambda) below the odd floor; root slope T_L'(a_j) = prod_{i != j}(a_i - a_j)/prod_k(b_k - a_j), nonzero with sign (-1)^{#{i : a_i < a_j}}"),
    "Zeta23/CCM/AbstractCubicSchur.lean": ("M08", "Step 34",
        "abstract cubic Schur formula s''' = a''' - 3<b', R b''> - 3<b'', R b'> + 6<b', R H' R b'> at a zero of b, symmetric and response forms, and the necessary sign s''' <= 0 at a stationary first-negative crossing"),
    "Zeta23/CCM/WeightedRemainderIdentity.lean": ("M09/M03", "Step 32; M03 staircase",
        "fixed staircase D(t) = 4 sinh(t/2) - B(t) for the pole-prime discrepancy (M03); zero-endpoint weighted remainder identity A_L[h] = int R(e^t) h' + int (e^{-t/2} - rho) h for C^1 tests with h(0) = h(L) = 0; at a stationary generated strict-even contact A_{L*}[t^2 e_{Dz}(1 - t/L*)] = -2 L*^4 C/(2 pi)^2 <= 0 with C = <A w, w>, and the exact contact-weighted remainder balance"),
    "Zeta23/CCM/CanonicalSourceOddEndpointQuantitative.lean": ("M45", "Step 82",
        "fifth-order sine Taylor bound; odd profile T_u = -M_3 t^3/6 + R_u with |R_u| <= B(u)|t|^5/120; 7/16 product bound; int t^3(a-t)^3 = a^7/140; Re e_u(omega) <= -(pi^6/90) |M_3(u)|^2 omega^7 for legal odd u when (2 pi omega)^2 B(u) <= 5|M_3(u)|, and on sourceAtomRealEnergy for 0 <= omega <= theta(u) = (1/2pi) sqrt(5|M_3|/(A_K ||u||)), A_K^2 = 2 sum n^10"),
    "Zeta23/CCM/CanonicalRecentPrimeSecondVariation.lean": ("M49", "Steps 84, 90",
        "at an even ground eigenvector with parity gap delta > 0, |v| = 1 and coercivity |v|^2 <= c |Dz|^2 (c = C_K or 4): for 0 <= omega with (2 pi omega)^2 A_K |H(v)| sqrt c <= 5 delta, e_{Dz}(omega) <= -(pi^6/90) |M_4|^2 omega^7 <= -(pi^6/90) (delta/(c |H(v)|))^2 omega^7; prime-term form on productionContactIndexEnergy"),
    "Zeta23/CCM/SourceRankTwoLaplace.lean": ("M03", "M03 Laplace (no separate step row)",
        "int_0^inf e^{-t/2} S_{nm}(t/L) dt = (8/L)(u_n u_m - a^2 v_n v_m), a = 4 pi/L; energy form (8/L)(|sum u x|^2 - a^2 |sum v x|^2); reversal-even PSD and reversal-odd NSD rank-one restrictions"),
}

PRINT = re.compile(r"(?m)^#print\s+axioms\s+(\S+)\s*$")


def proof_roots() -> dict:
    roots = []
    for src, (pkg, steps, scope) in MODULES.items():
        text = (REPO / src).read_text(encoding="utf-8")
        module = src[:-5].replace("/", ".")
        for decl in PRINT.findall(text):
            roots.append({
                "declaration": decl,
                "source": src,
                "module": module,
                "package": pkg,
                "steps": steps,
                "module_scope": scope,
                "status": "PROVED_PENDING_CI",
                "premises": [],
                "authority": "exact Lean theorem with its stated hypotheses; research-ledger root, not a registered claim",
                "axiom_receipt": "LOCAL_PASS_STANDARD_THREE",
            })
    return {
        "schema": "post285.proof_roots.v1",
        "terminal_claim": TERMINAL,
        "rule": "PROVED = exact clean Lean theorem with its full premises; status becomes PROVED only after the exact PR head passes the post-284 Lean/axiom/proof-escape jobs",
        "roots": roots,
    }


OBLIGATIONS = [
    {"id": "M70_SOURCE_EXCURSIONS", "package": "M70", "steps": "108",
     "status": "PROVED_PENDING_CI",
     "detail": "sourceEnergyRe_excursions_of_zeroSum: for nonzero zero-sum z the source energy e_{Dz} exceeds |z|^2/pi^2 and drops below -|z|^2/pi^2 on (0,1)."},
    {"id": "M71_INTERIOR_ANDREIEF_INERTIA", "package": "M71", "steps": "44, 109",
     "status": "PROVED_PENDING_CI",
     "detail": "evenBoundaryFlat_source_exactInertia / oddBoundaryFlat_source_exactInertia: for every 0 < omega <= 1/2 and K >= 2 the elementary source form on the even (odd) boundary-flat carrier is nondegenerate with exact inertia (K/2, (K-1)/2, 0) ((K-1)/2, K/2, 0). Proof: Andreief identity, signed leading minors (-1)^{r(r-1)/2} D_r > 0 in the cosine-power carrier basis (andreiefSign_mul_det_gram_pos), Jacobi split by Cramer vectors (jacobi_alternating_split), carrier Gram = Andreief convolution (sourceSesq_evenCarrier_cosPow, sourceSesq_oddCarrier_cosPow). Elementary sourceMatrix only; omega <= 1/2 (aperture a <= pi) is used and is not removable. Moment-filtered carriers (post-284 M18) are not covered."},
    {"id": "M72_SOURCE_SPECTRAL_FLOW_FIRST_PASSAGE", "package": "M72", "steps": "45, 110",
     "status": "PROVED_PENDING_CI",
     "detail": "exists_sourceDegenerate_of_half_neg / parityBoundaryFlat_sourceDegenerate: some omega in (1/2,1) makes the carrier source form PSD and degenerate. Zeros of source compression only."},
    {"id": "M72_SOURCE_SPECTRAL_FLOW_MULTIPLICITY", "package": "M72", "steps": "110",
     "status": "OPEN",
     "detail": "At least as many passages (with multiplicity) as half-aperture negative eigenvalues: DERIVED via continuous eigenvalue branches, not formalized."},
    {"id": "M73_QUARTER_POINCARE", "package": "M73", "steps": "89, 90, 115",
     "status": "PROVED_PENDING_CI",
     "detail": "sum_normSq_le_four_mul (and strict form): sum|z|^2 <= 4 sum n^2|z_n|^2 on the zero-sum carrier, uniform in K, via the telescoped mass 4 - 4/(2K+1). Contact gap delta|v|^2 <= 4|H(v)||M4(v)|."},
    {"id": "M73_QUARTER_SHARPNESS", "package": "M73", "steps": "115",
     "status": "EXPERIMENTAL_SIGNAL",
     "detail": "Optimal constant on the whole zero-sum carrier decreases to 1/4 numerically (0.2513 at K=80). Not proved; no sharpness claimed on the even legal carrier."},
    {"id": "M74_CANONICAL_SECULAR_RESOLVENT", "package": "M74", "steps": "49-52, 111, 112, 116-118",
     "status": "PROVED_PENDING_CI",
     "detail": "Canonical instance of the rank-one secular algebra with the actual A_L, B_L, D, g, H_L: resolvent ray, relative determinant, ker A_L = span(x_L) iff H_L(x_L) = 1, Ward identity, contact phase lock Re(conj S M4) = gamma|S|^2 > 0, approximate-contact bounds, M4 gauge. D is not assumed unitary. H_L(x_L) = 1 is contact-equivalent and is never used as an independent opposite-side input."},
    {"id": "M75_SOURCE_LIPSCHITZ_AND_WINDOW", "package": "M75", "steps": "119",
     "status": "PROVED_PENDING_CI",
     "detail": "abs_sourceEnergyRe_index_sub_le (M_K = (2+4 pi K)(2K+1)K^2) and exists_sourceNegativeWindow (e < -|z|^2/(2 pi^2) on |omega - omega_-| <= 1/(2 pi^2 M_K), window inside (0,1))."},
    {"id": "M75_OPPOSITE_SIGNED_PRIME_SUMMANDS", "package": "M75", "steps": "120",
     "status": "PROVED_PENDING_CI",
     "detail": "exists_prime_physicalSecondPrimeTerm_pos_and_two_neg: for L >= pi^2 M_K log 2 some prime 2 < p < e^L has a strictly positive physical second-test summand -(Lambda(p)(log p)^2/sqrt p) e(1 - log p/L) and the p = 2 summand is strictly negative. Individual summands only; no statement about the prime sum."},
    {"id": "M26_M27_CANONICAL_SHIFTED_SECULAR", "package": "M26/M27", "steps": "58, 59, 64",
     "status": "PROVED_PENDING_CI",
     "detail": "For real lambda below the odd Rayleigh bottom: (A_L - lambda) v_L(lambda) = (1 - T_L(lambda)) D^-1 g, det(A_L - lambda) = det(B_L - lambda)(1 - T_L(lambda)), lambda is an even eigenvalue iff T_L(lambda) = 1, and the even eigenspace at lambda has finrank <= 1 (canonical_finrank_eigenspace_le_one). T_L(lambda) = 1 is the eigenvalue condition itself."},
    {"id": "M27_ALTERNATING_ROOT_SLOPES", "package": "M27", "steps": "59",
     "status": "PROVED_PENDING_CI",
     "detail": "one_sub_canonicalSecularFunction_eq: below the odd Rayleigh bottom 1 - T_L(lambda) = prod_i(a_i - lambda)/prod_k(b_k - lambda) over the eigenvalues of A_L and B_L. canonical_secular_hasDerivAt_root: at every even eigenvalue a_j below the odd floor T_L'(a_j) = prod_{i != j}(a_i - a_j)/prod_k(b_k - a_j). canonical_secular_root_slope_sign: that slope is nonzero with sign (-1)^{#{i : a_i < a_j}}, i.e. (-1)^(j-1) for the roots numbered increasingly. Fixed L only: no lambda-monotonicity away from the roots and no aperture-derivative sign is claimed."},
    {"id": "M28_CONTACT_OVERLAP_IDENTITY", "package": "M28", "steps": "60",
     "status": "PROVED_PENDING_CI",
     "detail": "canonical_contact_overlap: at an even contact with positive odd bottom, <x_L, D^-1 g> * S_L(D^-1 B_L^-1 B_L^-1 g) = |x_L|^2, so both factors are nonzero, and |x_L| <= |D^-1 g| |S_L(w_L)|. Sign-free."},
    {"id": "M28_OVERLAP_POSITIVITY", "package": "M28", "steps": "60",
     "status": "PROVED_PENDING_CI",
     "detail": "canonical_contact_overlap_pos: at an even contact (S_L(x_L) = 1) with 0 <= even Rayleigh bottom and 0 < odd Rayleigh bottom, S_L(w_L) and <x_L, D^-1 g> are real and strictly positive. Route: coercive symmetric maps have real positive determinants, so 1 - T_L(lambda) > 0 for lambda < 0; the resolvent identity and an elementary limit lambda -> 0-. A_L positive semidefinite is a hypothesis (first-crossing geometry), never inferred from T <= 1; nothing asserts that a contact exists."},
    {"id": "M14_ODD_FIRST_AND_TIED_BRANCH_ALGEBRA", "package": "M14/M77", "steps": "global branch analysis",
     "status": "PROVED_PENDING_CI",
     "detail": "Swapped rank-one instance A D^-1 - D^-1 B = (-D^-1 g) (x) (H o D^-1). With positive even bottom: ker B_L lies on span(D A_L^-1 D^-1 g) (finrank <= 1), B_L singular iff S_L(A_L^-1 D^-1 g) = -1, det B_L = det A_L (1 + S_L(A_L^-1 D^-1 g)). Tied: A_L z = 0 and B_L y = 0 imply S_L(z) <g, y> = 0. Identities only; no branch is excluded."},
    {"id": "M14_BRANCH_EXCLUSION", "package": "M14", "steps": "global branch analysis",
     "status": "OPEN",
     "detail": "No even-first, odd-first, tied, fresh-born or interior branch is excluded. The contact criteria above are equivalent to the contacts themselves."},
    {"id": "M65_PRIME_FREE_F04", "package": "M65", "steps": "21, 24, 27, 93, 101, 103, 105",
     "status": "PROVED_PENDING_CI",
     "detail": "productionContactF04DerivativeAuthority_of_lt_log_two: for 0 < L < log 2 and every K, all three fields of ProductionContactF04DerivativeAuthority L K hold for the actual canonical even compressed family: E'_z = A_L[(t/L^2) e'_z(1 - t/L)], E''_z + (2/L) E'_z = A_L[(t^2/L^4) e''_z(1 - t/L)], Re<z, A'_L w> = A_L[mixed test]. Proof: real M05 identity with no prime terms below log 2, Leibniz under the moving aperture with t rho(t) regularized, endpoint cancellation via wCorrection' = e^{-L/2} rho(L), e'_z(0) = 0 on boundary-flat vectors, symmetric polarization for the mixed field. The single cCorrection repair is the one inside canonicalSourceMatrix; nothing is added twice."},
    {"id": "F04_GLOBAL_PRODUCTION_DERIVATIVE_AUTHORITY", "package": "M06/M53", "steps": "21, 24, 27, 93, 101, 105",
     "status": "PROVED_PENDING_CI",
     "detail": "productionContactF04DerivativeAuthority_of_pos: all three F04 fields hold at every L > 0 and every K. Over a fixed range of q the prime staircase is a sum of terms switched on by log q <= L; each entering term has zero value and slope at its seam because e_z(0) = e'_z(0) = 0 (energy) and e'_z(0) = e''_z(0) = 0 (first channel) on boundary-flat vectors, so it is differentiable there (hasDerivAt_ite_le). Statement: forall K L, 0 < L -> ProductionContactF04DerivativeAuthority L K, the exact post-284 premise structure, with no other hypothesis. All ten Zeta23/CCM consumers have F04-free instances here (*_of_pos, *_unconditional); the eight RHRC claim-contract wrappers still take hF04 as a parameter until the registry is rebound. Derivative transport only: no sign, no contact exclusion."},
    {"id": "STEP103_STATIONARY_SECOND_VALUE", "package": "M65/M66", "steps": "103",
     "status": "PROVED_PENDING_CI",
     "detail": "GeneratedStrictEvenContact.secondPhysicalValue_eq_two_mul_responseCost / secondPhysicalValue_nonneg: at a stationary generated strict-even contact the complete second physical value (pole, archimedean and every prime up to e^{L*}) equals 2<A w, w> >= 0 for the stationary response w."},
    {"id": "F04_CONDITIONAL_FRONTIER_UNCONDITIONAL", "package": "M65/F07", "steps": "19, 27, 74",
     "status": "PROVED_PENDING_CI",
     "detail": "production_stationary_saturation, production_stationary_remainder_pos, completed_production_frontier and inherited_completed_production_frontier of FirstCrossingGeneratedStrictEvenFrontier now hold with no F04 hypothesis (*_unconditional). The stationary production remainder is strictly positive at every stationary generated strict-even contact; excluding that saturation (OBS-060O) stays OPEN."},
    {"id": "M66_PRIME_FREE_EULER_NEGATIVITY", "package": "M66", "steps": "102, 103",
     "status": "PROVED_PENDING_CI",
     "detail": "productionSecondDerivativePhysicalValue_eq_neg_primeFreeSecondTest (Q-F04: E''_z + (2/L) E'_z = -(2 pi)^2/L^4 Q_K(L, z) for 0 < L < log 2), productionContactEulerCurvature_le (<= -(M/L^2)(1 - 2 pi^2 L (2K+1) K^2), M = sum|z_i|^2) and productionContactEulerCurvature_neg (< 0 for nonzero z on 0 < L < eps_K = 1/(2 pi^2 (2K+1) K^2)). Even boundary-flat carrier only."},
    {"id": "M66_LOCAL_STATIONARY_EXCLUSION", "package": "M66", "steps": "74, 104",
     "status": "PROVED_PENDING_CI",
     "detail": "GeneratedStrictEvenContact.firstVariation_ne_zero_of_lt_primeFreeRadius and fresh_of_lt_primeFreeRadius: a generated strict-even contact with L* < eps_K is not stationary, hence fresh-born. Possibly vacuous: numerically the even ground is positive on the whole prime-free window for K = 2..16, so no generated contact is known to lie below eps_K. Excludes nothing above eps_K and says nothing about odd-first, tied or interior branches."},
    {"id": "M66_EULER_RADIUS_SIGNAL", "package": "M66", "steps": "104",
     "status": "EXPERIMENTAL_SIGNAL",
     "detail": "On the even boundary-flat carrier the Euler-corrected form E'' + (2/L)E' stays negative definite up to about L = 0.55 (K = 2), 0.42 (K = 3), 0.38 (K = 4), 0.36 (K = 5), 0.30 (K = 16), against eps_K = 2.5e-3 .. 2.3e-5. Floating point only."},
    {"id": "M55_WEIGHTED_CHEBYSHEV_PARTIAL_SUMMATION", "package": "M55", "steps": "96",
     "status": "PROVED_PENDING_CI",
     "detail": "psi_sub_self_eq_weightedRemainder: for real x >= 1, psi(x) - x = 1 + sqrt(x) R(x) - (1/2) int_1^x R(t)/sqrt(t) dt with R(x) = sum_{n <= x} Lambda(n)/sqrt(n) - 2 sqrt(x) (Mathlib Abel summation, right-continuous floor convention). abs_psi_sub_self_sub_one_le: |R| <= M on [1, x] gives |psi(x) - x - 1| <= 2 M sqrt(x). Firewall: R = O_eps(x^eps) for every eps > 0 would be RH-strength; it is never assumed. Unconditional; no sign or size of R."},
    {"id": "M38_FINITE_REMAINDER_EXTREMA", "package": "M38", "steps": "75",
     "status": "PROVED_PENDING_CI",
     "detail": "isGreatest_weightedRemainder: sup_{[1,X]} R = max_{1 <= m <= floor X} R(m), attained. isGLB_weightedRemainder: inf_{[1,X]} R = min_{1 <= m <= floor X} (W_m - 2 sqrt(min(m+1, X))), stated as a greatest lower bound because it can be a left limit before a jump. Finite arithmetic; the oscillation Omega(L) of (71.2) is now a finite computation. No bound on Omega(L) is claimed."},
    {"id": "M31_GRONWALL_BARRIER", "package": "M31", "steps": "66",
     "status": "PROVED_PENDING_CI",
     "detail": "gronwall_lower_bound / gronwall_pos: y' >= -C y on (a, b) with C continuous gives y(t) >= y(a) exp(-int_a^t C). canonical_evenBottom_pos_of_gronwall (CONDITIONAL): odd bottom > 0 on [L0, L1], even bottom > 0 at L0, det A_L = det B_L y(L), and y' >= -C y imply the even bottom stays positive on [L0, L1]. The Gronwall inequality is a hypothesis; it is the OPEN M32 target. Not an exclusion theorem."},
    {"id": "M08_ABSTRACT_CUBIC_SCHUR", "package": "M08", "steps": "34",
     "status": "PROVED_PENDING_CI",
     "detail": "cubic_schur_third_deriv: for C^3 families a, b, H (real inner product space; complex Hermitian through Re<.,.>) with H(t0) invertible, R = H(t0)^-1 and b(t0) = 0, s = a - <b, H^-1 b> has s'''(t0) = a''' - 3<b', R b''> - 3<b'', R b'> + 6<b', R H' R b'>. cubic_schur_third_deriv_response: for symmetric H(t0), s''' = a''' - 6<b', R b''> + 6<R b', H' R b'> = a''' + 6<b'', w> + 6<H' w, w> with w = -R b'. cubic_schur_third_nonpos_of_right_negative: a zero of order three that turns negative to the right has s''' <= 0 (necessary only)."},
    {"id": "M09_ZERO_ENDPOINT_WEIGHTED_REMAINDER", "package": "M09", "steps": "32",
     "status": "PROVED_PENDING_CI",
     "detail": "regularizedCompletePhysicalRHS_eq_weightedRemainder (integrability premises explicit) and the C^1 forms productionArithmeticComplexValue_eq_weightedRemainder / productionArithmeticRealValue_eq_weightedRemainder: for h(0) = h(L) = 0, A_L[h] = int_0^L R(e^t) h'(t) dt + int_0^L (e^{-t/2} - rho(t)) h(t) dt with R(x) = sum_{n <= x} Lambda(n)/sqrt n - 2 sqrt x. Finite summation by parts on the prime staircase plus one integration by parts on the pole main term. The endpoint h(0) = 0 removes the M05 scalar correction; nonzero-endpoint energies keep it. productionArithmeticRealValue_sq_mul_indexEnergy_eq_weightedRemainder specializes to t^2 e_{Dz}(1 - t/L)."},
    {"id": "M09_CONTACT_WEIGHTED_BALANCE", "package": "M09", "steps": "32",
     "status": "PROVED_PENDING_CI",
     "detail": "GeneratedStrictEvenContact.indexEnergyValue_eq_neg_responseCost / indexEnergyValue_nonpos / weightedRemainder_balance: at a stationary generated strict-even contact (simple even kernel, positive odd complement, normalized z, stationary response w with A w = -A' z) A_{L*}[t^2 e_{Dz}(1 - t/L*)] = -2 L*^4 C/(2 pi)^2 <= 0 with C = <A w, w> >= 0, and the same value equals int R(e^t)(2t e_{Dz} - (t^2/L*) e'_{Dz}) + int (e^{-t/2} - rho) t^2 e_{Dz}. Uses F04 at every L > 0 (CanonicalGlobalF04, pending CI). A necessary condition, not a contradiction; no sign of R is used."},
    {"id": "M03_FIXED_STAIRCASE_REEXPRESSION", "package": "M03", "steps": "M03 (no separate step row)",
     "status": "PROVED_PENDING_CI",
     "detail": "canonicalPolePrimeDiscrepancy_eq_fixedStaircase: for t <= L the canonical pole-prime discrepancy is D(t) = 4 sinh(t/2) - B(t) with the aperture-free staircase B(t) = weightedVonMangoldtSqrtSum (e^t) (right-continuous: q counted at log q <= t; zero-von-Mangoldt integers contribute nothing). matrixRealEnergy_pole_sub_prime_eq_fixedStaircase: the pole-minus-prime energy is (1/L) int_0^L D(t) e'_u(1 - t/L) dt in the existing normalization. Reuses CanonicalPrimeRemainder and CanonicalPolePrimeDiscrepancy; no new staircase object."},
    {"id": "M03_RANK_TWO_LAPLACE_TRANSFORM", "package": "M03", "steps": "M03 (no separate step row)",
     "status": "PROVED_PENDING_CI",
     "detail": "integral_exp_neg_half_mul_sourceEntryReal: for L > 0 and all centered n, m (diagonal and off-diagonal), int_0^inf e^{-t/2} S_{nm}(t/L) dt = (8/L)(u_n u_m - a^2 v_n v_m) with a = 4 pi/L, u_n = 1/(1 + a^2 n^2), v_n = n/(1 + a^2 n^2). integral_exp_neg_half_mul_sourceEnergy: the weighted energy of complex coefficients x is (8/L)(|sum u_i x_i|^2 - a^2 |sum v_i x_i|^2). _of_even / _of_odd: reversal-even x give (8/L)|sum u x|^2 >= 0, reversal-odd x give -(8/L) a^2 |sum v x|^2 <= 0. Improper integrals via e^{ct} and t e^{ct} with c = -1/2 + i beta. Semidefinite rank-one restrictions of a model transform, not definiteness and not the canonical energy."},
    {"id": "M45_ODD_ENDPOINT_QUANTITATIVE", "package": "M45", "steps": "82",
     "status": "PROVED_PENDING_CI",
     "detail": "re_quadraticForm_sourceMatrix_le_of_mem_oddBoundaryFlat: for u in oddBoundaryFlatSubspace K and 0 <= omega with (2 pi omega)^2 B(u) <= 5 |M_3(u)|, B(u) = sum |n|^5 |u_n|, Re e_u(omega) <= -(pi^6/90) |M_3(u)|^2 omega^7 on the actual sourceMatrix (complex coefficients). Strict form for M_3(u) != 0 and omega > 0; aperture form Re e_u(a/2pi) <= -7 m^2 a^7/(80640 pi). sourceAtomRealEnergy_le_of_le_oddEndpointAngle: the same on sourceAtomRealEnergy for 0 <= omega <= theta(x) = (1/2pi) sqrt(5|M_3|/(A_K ||x||)), with A_K^2 = 2 sum_{n=1}^K n^10 (sourceOddTaylorConstant_sq) and B(u) <= A_K ||u|| (sourceOddTaylorWeight_le). Elementary source statement only: no contact transfer (M46 theta_*), no prime estimate, no sign of the canonical arithmetic test."},
    {"id": "M49_NEAR_EDGE_PRIME_BENEFIT", "package": "M49", "steps": "84, 90",
     "status": "PROVED_PENDING_CI",
     "detail": "sourceAtomRealEnergy_index_le_of_contactAngle(_coercivity/_four): at an even ground eigenvector v of the actual canonical even compression with parity gap delta > 0 and |v| = 1, Dz is legal odd with M_3(Dz) = M_4(z); for 0 <= omega with (2 pi omega)^2 A_K |H(v)| sqrt c <= 5 delta (c = C_K from M46 or 4 from M73), e_{Dz}(omega) <= -(pi^6/90) |M_4|^2 omega^7 <= -(pi^6/90) (delta/(c |H(v)|))^2 omega^7. primeTerm_ge_of_contactAngle_four: each prime term -beta e_{Dz}(omega_q) of productionContactIndexEnergy with beta >= 0 and omega_q in that angle is >= (pi^6/90) beta (delta/(4 |H(v)|))^2 omega_q^7. |H(v)| <= B_H only enlarges the plan's angle. Individual near-edge terms only: older primes, the pole/archimedean part and the complete test are not addressed (M50, M51 OPEN); the angle may contain no sample."},
    {"id": "M08_ARITHMETIC_THIRD_IDENTITY", "package": "M08", "steps": "34",
     "status": "OPEN",
     "detail": "<F''' z, z> = -(2 pi)^2 A_L[t^3 e'_{Dz}(1 - t/L)]/L^6 - 12 C/L and the conditional necessary inequality need moving-aperture C^3 transport of the full source on a neighborhood; not formalized."},
    {"id": "M32_CANONICAL_GRONWALL_COEFFICIENT", "package": "M32", "steps": "66, 67",
     "status": "OPEN",
     "detail": "No independent continuous or integrable C_K with T_L' <= C_K(L)(1 - T_L) is known for the canonical operator. C_K may not be built from T'/(1 - T), det A_L, assumed absence of contacts, or RH."},
    {"id": "M76_ARITHMETIC_COMPOSITION", "package": "M76", "steps": "113, 120",
     "status": "OPEN",
     "detail": "Contact-conditioned opposite-side inequality for the complete source-moment arithmetic remains OPEN. The M75 mixed individual signs exclude termwise prime positivity; they are not an RH contradiction."},
    {"id": "OBS060O_STATIONARY_SATURATION_EXCLUSION", "package": "M13", "steps": "74, 104",
     "status": "OPEN", "detail": "Unchanged by this PR."},
    {"id": "M77_INTEGRATION", "package": "M77", "steps": "107, 114",
     "status": "IN_PROGRESS",
     "detail": "Ledgers, workflow targets, axiom audit and proof-escape receipts for M70-M75, M26-M28, M65, M66 and the branch algebra in this PR; the #285 cleanup PR #286 has merged and this branch is rebased on it. The two F04-bound #284 claims (R003_WEIGHTED_PRODUCTION_PAIR_BALANCE, R003_COMPLETED_STRICT_EVEN_CONTACT_FRONTIER) stay OPEN in the registry until CI is green on this head; their unconditional versions are canonicalSecondPairing_euler_eq_productionSaturationGap_of_pos and GeneratedStrictEvenContact.completed_production_frontier_unconditional."},
    {"id": "RH", "package": "terminal", "steps": "-", "status": "OPEN", "detail": "RH_OPEN."},
]

POST284_CROSS_REFERENCES = [
    {"post284_id": "M17_GENERAL_OMEGA_ANDREIEF_INERTIA", "effect": "proved here for every 0 < omega <= 1/2 on the even and odd boundary-flat carriers (M71_INTERIOR_ANDREIEF_INERTIA, pending CI); the post-284 ledger entry is historical and unchanged; filtered carriers stay OPEN"},
    {"post284_id": "M18_SPECTRAL_FLOW_PASSAGES", "effect": "first passage proved here (M72_SOURCE_SPECTRAL_FLOW_FIRST_PASSAGE); multiplicity count still OPEN"},
    {"post284_id": "F_M21_PHASE_LOCK", "effect": "canonical contact phase identity proved here (canonical_contact_phase, M74); contact existence and its sign consequences still OPEN"},
    {"post284_id": "F_M58_M63_SOURCE_MOMENT_BIRDFISHIE", "effect": "M58 phase-lock component discharged by M74; M61-M63 OPEN"},
    {"post284_id": "F_M46_COERCIVITY", "effect": "constant improved from C_K < 5 to 4 (M73)"},
    {"post284_id": "F_M53_M65_F04_DERIVATIVES", "effect": "proved here: prime-free (M65_PRIME_FREE_F04) and at every L > 0 (F04_GLOBAL_PRODUCTION_DERIVATIVE_AUTHORITY)"},
    {"post284_id": "F04_PRODUCTION_DERIVATIVE_AUTHORITY", "effect": "proof constructor productionContactF04DerivativeAuthority_of_pos proved here for every L > 0 and K"},
    {"post284_id": "F_M33_M34_CONTACT_SOURCE_SIGN_AND_BUDGET", "effect": "F04 at the contact boundary now available (F04_GLOBAL_PRODUCTION_DERIVATIVE_AUTHORITY); the sign and budget statements are not formalized here"},
    {"post284_id": "F_M48_K2_PRIME_SAMPLES", "effect": "F04 premise of the contact consequence P = -F <= 0 discharged; the consequence itself is not formalized here"},
    {"post284_id": "F_M49_M51_NEAR_EDGE_AND_OLDER_PRIME", "effect": "F04 dependency discharged; the M45 elementary source bound and the M49 near-edge contact-angle bound are proved here (M45_ODD_ENDPOINT_QUANTITATIVE, M49_NEAR_EDGE_PRIME_BENEFIT, pending CI); the M50 older-prime budget and M51 stay OPEN"},
    {"post284_id": "F_M45_ODD_ENDPOINT_QUANTITATIVE", "effect": "proved here (M45_ODD_ENDPOINT_QUANTITATIVE, pending CI) on the actual sourceMatrix and sourceAtomRealEnergy, with the plan's angle theta(u) and constant pi^6/90"},
    {"post284_id": "F_M37_LOCAL_EXCLUSION", "effect": "F04 premise discharged below log 2; unconditional stationary exclusion below eps_K proved here (M66_LOCAL_STATIONARY_EXCLUSION, possibly vacuous)"},
    {"post284_id": "F_M66_NEG_EULER_AND_LOCAL_EXCLUSION", "effect": "proved here (M66_PRIME_FREE_EULER_NEGATIVITY, M66_LOCAL_STATIONARY_EXCLUSION)"},
    {"post284_id": "M09_WEIGHTED_REMAINDER_IDENTITY", "effect": "proved here (M09_ZERO_ENDPOINT_WEIGHTED_REMAINDER, M09_CONTACT_WEIGHTED_BALANCE, pending CI); the contact-weighted balance uses F04 at every L > 0 and is a necessary condition, not an exclusion"},
    {"post284_id": "M03_WEIGHTED_STAIRCASE_REEXPRESSION", "effect": "proved here (M03_FIXED_STAIRCASE_REEXPRESSION, pending CI)"},
    {"post284_id": "M16_SMALL_OMEGA_LEGAL_FORM_INDEFINITENESS", "effect": "subsumed here by M71: parityBoundaryFlat_source_indefinite gives positive and negative even and odd boundary-flat vectors at every 0 < omega <= 1/2 for K >= 3 (pending CI); the K3 moving-vector coefficients stay exact controls"},
    {"post284_id": "M03_RANK_TWO_LAPLACE", "effect": "proved here (M03_RANK_TWO_LAPLACE_TRANSFORM, pending CI); the post-284 F07 regression (5e-29) stays the numerical check"},
    {"post284_id": "F_M27_ALTERNATING_SLOPES", "effect": "proved here: canonical shifted secular equation and simple even roots below the odd floor (M26_M27_CANONICAL_SHIFTED_SECULAR) and the alternating root-slope formula (M27_ALTERNATING_ROOT_SLOPES, pending CI)"},
    {"post284_id": "F_M28_RESOLVENT_OVERLAP", "effect": "exact overlap identity (M28_CONTACT_OVERLAP_IDENTITY) and positivity when A_L is positive semidefinite and B_L positive definite (M28_OVERLAP_POSITIVITY) proved here"},
    {"post284_id": "F_M55_ABEL_SUMMATION", "effect": "proved here (M55_WEIGHTED_CHEBYSHEV_PARTIAL_SUMMATION), with the transfer bound that makes the RH-strength firewall explicit"},
    {"post284_id": "F_M38_REMAINDER_EXTREMA", "effect": "proved here (M38_FINITE_REMAINDER_EXTREMA)"},
    {"post284_id": "F_M31_ABSTRACT_GRONWALL", "effect": "abstract Gronwall bound and the canonical even-bottom barrier proved here (M31_GRONWALL_BARRIER); the barrier is conditional on the OPEN inequality (M32_CANONICAL_GRONWALL_COEFFICIENT)"},
    {"post284_id": "M14_OTHER_BRANCHES", "effect": "odd-first and tied branch algebra proved here (M14_ODD_FIRST_AND_TIED_BRANCH_ALGEBRA); no branch excluded"},
    {"post284_id": "M08_ABSTRACT_CUBIC_SCHUR", "effect": "abstract cubic Schur formula, response form and necessary sign proved here (M08_ABSTRACT_CUBIC_SCHUR, pending CI); the arithmetic third identity stays OPEN (M08_ARITHMETIC_THIRD_IDENTITY)"},
]


def open_obligations() -> dict:
    return {
        "schema": "post285.open_obligations.v1",
        "terminal_claim": TERMINAL,
        "authority": "REPORTING_LEDGER",
        "note": "The post-284 ledger is not edited by this PR. Its PR #285 rows were promoted by the merged #285 cleanup PR #286, whose statuses are authoritative for every #285 entry.",
        "obligations": OBLIGATIONS,
        "post284_cross_references": POST284_CROSS_REFERENCES,
    }


# Steps 18-120.  status vocabulary:
# PROVED_THIS_PR (pending CI), PROVED_MERGED (in main via #284/#285),
# PARTIAL (a named part proved, rest open), CONDITIONAL, DERIVED,
# INTERVAL_EVIDENCE, EXPERIMENTAL_SIGNAL, OPEN, SCOPE_CONTROL.
STEPS = {
    18: ("Current canonical baseline / contact definitions", "M00", "PROVED_MERGED", "baseline definitions and global compressed C2 (#284)"),
    19: ("Inherited stationarity and first contact", "M00", "PROVED_MERGED", "FirstCrossingGeneratedStrictEvenFrontier"),
    20: ("Schur geometry and optimized response", "M00", "PROVED_MERGED", "StationarySchurContact / FirstCrossingProductionResponse"),
    21: ("Production derivative authority interface", "M06/M65", "PROVED_THIS_PR", "constructor productionContactF04DerivativeAuthority_of_pos at every L > 0"),
    22: ("Physical pole/arch/prime normalization", "M05", "PROVED_MERGED", "CanonicalRegularizedEnergyIdentity (#285)"),
    23: ("Exact finite source and zero-endpoint jets", "M07", "PROVED_MERGED", "source-coordinate jets; operator seam Taylor estimates open"),
    24: ("Aperture derivatives and source transport", "M06/M65", "PROVED_THIS_PR", "prime-free window (CanonicalPrimeFreeF04) and prime cells and seams (CanonicalGlobalF04)"),
    25: ("Contact generation from a first bad state", "M00", "PROVED_MERGED", "generated contact frontier"),
    26: ("Contact directional first variation", "M00", "PROVED_MERGED", "production first variation"),
    27: ("F04-weighted contact response reduction", "M09/M65", "PROVED_THIS_PR", "unconditional at every L > 0 (canonicalSecondPairing_euler_eq_productionSaturationGap_of_pos)"),
    28: ("Exploratory sign witnesses and falsification", "M12", "EXPERIMENTAL_SIGNAL", "research only"),
    29: ("Two-scalar stationary curvature identity", "M03", "OPEN", "M03_TWO_SCALAR_CONTACT_TRANSPORT"),
    30: ("Fourier-convolution source identity", "M04", "PROVED_MERGED", "SourceFourierConvolution (#285)"),
    31: ("K=3 exact source counterexample", "M04", "PROVED_MERGED", "SourceSignCountermodels (#285)"),
    32: ("Von Mangoldt discrepancy and weighted balance", "M09", "PROVED_THIS_PR", "zero-endpoint identity (regularizedCompletePhysicalRHS_eq_weightedRemainder, productionArithmeticRealValue_eq_weightedRemainder); contact balance A_{L*}[t^2 e_{Dz}] = -2 L*^4 C/(2 pi)^2 <= 0 (GeneratedStrictEvenContact.weightedRemainder_balance); necessary condition only"),
    33: ("Ninth-order even seam jump", "M10", "OPEN", "M10_NINTH_ORDER_OPTIMIZED_SCHUR_JUMP"),
    34: ("Third derivative Schur and arithmetic bridge", "M08", "PARTIAL", "abstract cubic Schur PROVED_THIS_PR (cubic_schur_third_deriv, cubic_schur_third_deriv_response, cubic_schur_third_nonpos_of_right_negative); arithmetic third identity OPEN"),
    35: ("Analytic first-crossing seam dichotomy", "M11", "CONDITIONAL", "StrictEvenPrimeSeamDichotomy: premises explicit"),
    36: ("Finite source-moment filtration", "M15", "PROVED_MERGED", "SourceMomentVandermondeFiltration (#285)"),
    37: ("Boundary-flat hierarchy of source moments", "M15", "PROVED_MERGED", "SourceMomentVandermondeFiltration (#285)"),
    38: ("Nonvanishing first source jets", "M15", "PROVED_MERGED", "first-jet signs (#285)"),
    39: ("Moving legal negative/positive source witnesses", "M16/M71", "PROVED_THIS_PR", "small-omega legal-form indefiniteness subsumed by parityBoundaryFlat_source_indefinite (every 0 < omega <= 1/2, K >= 3); K3 moving-vector coefficients remain exact controls"),
    40: ("Moving-ray sign countercontrols", "M16", "PROVED_MERGED", "exact controls in SourceSignCountermodels (#285)"),
    41: ("Gap-driven fourth-moment rigidity", "M19", "PROVED_MERGED", "inequality form (ContactNinthJumpGapBound); M73 improves constant"),
    42: ("Higher-moment source signs and limits", "M15/M18", "DERIVED", "not separately formalized"),
    43: ("Parity polynomial reduction", "M17", "PROVED_MERGED", "SourceParityPolynomialCoordinates (#285)"),
    44: ("Andreief signed-minor inertia target", "M17/M71", "PROVED_THIS_PR", "omega = 1/2 PROVED (#285); every 0 < omega <= 1/2: andreiefSign_mul_det_gram_pos, evenBoundaryFlat_source_exactInertia, oddBoundaryFlat_source_exactInertia"),
    45: ("Source spectral flow after half aperture", "M18/M72", "PARTIAL", "first passage PROVED_THIS_PR; multiplicity OPEN"),
    46: ("Filtered parity moment carriers", "M18", "PROVED_MERGED", "half-aperture filtered inertia (#285)"),
    47: ("Fourth-moment nonzero sign firewall", "M18", "PROVED_MERGED", "fourth-moment firewall (#285)"),
    48: ("Full canonical vs elementary source separation", "M18", "SCOPE_CONTROL", "firewall, no theorem"),
    49: ("Canonical rank-one resolvent scalar", "M20/M74", "PROVED_THIS_PR", "canonical_rankOneIntertwining, canonicalResolventGamma_pos"),
    50: ("Strict-even threshold contact criterion", "M20/M74", "PROVED_THIS_PR", "canonical_resolventRay_contact_iff, canonical_ker_eq_span_of_contact"),
    51: ("Canonical phase locking of source and moment", "M21/M74", "PROVED_THIS_PR", "canonical_contact_phase (contact-conditioned identity)"),
    52: ("Odd resolvent spectral-gap bound", "M21/M74", "PROVED_THIS_PR", "canonical_resolventVector_norm_le"),
    53: ("Secular-Schur stationary-jet transport", "M22", "OPEN", "jets require hypotheses"),
    54: ("Entering seventh-order odd prime atom", "M23", "OPEN", "operator upgrade needed"),
    55: ("Matched rank-one cancellation", "M24", "PROVED_MERGED", "abstract matched update (SecularDeterminantKernel, #285)"),
    56: ("Surviving ninth-order seam threshold jump", "M24", "OPEN", "one-sided operator germs"),
    57: ("Exact cubic stationary crossing falsifier", "M30", "PROVED_MERGED", "2x2 crossing negative control (#285); re-run against M74 identities here"),
    58: ("Shifted spectral-parameter secular equation", "M26", "PROVED_THIS_PR", "abstract (#285); canonical instance canonical_shifted_det_eq / canonical_shifted_apply_ray"),
    59: ("Spectral root derivative and simplicity", "M27", "PROVED_THIS_PR", "simplicity (canonical_finrank_eigenspace_le_one); root slope and alternating sign (canonical_secular_hasDerivAt_root, canonical_secular_root_slope_sign)"),
    60: ("Contact resolvent overlap identity", "M28", "PROVED_THIS_PR", "identity (canonical_contact_overlap) and positivity with A_L >= 0, B_L > 0 (canonical_contact_overlap_pos)"),
    61: ("Source-resolvent aperture derivative", "M29", "OPEN", ""),
    62: ("Second source-resolvent balance", "M29", "OPEN", ""),
    63: ("Third-order source-resolvent obstruction", "M29", "OPEN", ""),
    64: ("Simplicity of all even roots below odd floor", "M27", "PROVED_THIS_PR", "canonical_finrank_eigenspace_le_one (geometric multiplicity <= 1; A_L symmetric)"),
    65: ("Abstract stationary cubic crossing countermodel", "M30", "PROVED_MERGED", "(#285)"),
    66: ("Differential Gronwall contact barrier", "M31", "CONDITIONAL", "abstract bound gronwall_lower_bound PROVED_THIS_PR; canonical barrier canonical_evenBottom_pos_of_gronwall conditional on (67.1), which is OPEN (M32)"),
    67: ("Full arithmetic derivative inequality target", "M32", "OPEN", ""),
    68: ("Odd source-sign reversal of contact vector", "M33", "OPEN", ""),
    69: ("Physical second-order sign-changing test", "M33/M41", "INTERVAL_EVIDENCE", "M41 interval enclosure (#285)"),
    70: ("Exact archimedean density and remainder", "M34", "OPEN", ""),
    71: ("Stationary arithmetic remainder oscillation", "M34", "OPEN", ""),
    72: ("Weighted elementary source integral", "M35", "PROVED_MERGED", "CanonicalSourceWeightedIntegral (#285)"),
    73: ("Uniform small-aperture physical positivity", "M36", "PROVED_MERGED", "fixed-vector test only (#285)"),
    74: ("Conditional local stationary contact contradiction", "M37/M66", "PARTIAL", "unconditional below eps_K PROVED_THIS_PR (firstVariation_ne_zero_of_lt_primeFreeRadius, possibly vacuous); above eps_K OPEN"),
    75: ("Finite extrema of logarithmic prime remainder", "M38", "PROVED_THIS_PR", "isGreatest_weightedRemainder (attained at an integer), isGLB_weightedRemainder (possibly a left limit)"),
    76: ("Contact sign scope and next arithmetic target", "M39", "OPEN", ""),
    77: ("General negative integrated source operator", "M40", "PROVED_MERGED", "(#285)"),
    78: ("K2 prime-free physical test falsifier", "M41", "INTERVAL_EVIDENCE", "(#285)"),
    79: ("Explicit finite-K initial positive radius", "M42", "PROVED_MERGED", "fixed-vector test (#285)"),
    80: ("K3 indefinite physical second-order test", "M43", "INTERVAL_EVIDENCE", "(#285)"),
    81: ("Entering seventh-order prime second-test sign", "M44", "OPEN", ""),
    82: ("Explicit odd endpoint source Taylor bound", "M45", "PROVED_THIS_PR", "Re e_u(omega) <= -(pi^6/90) |M_3(u)|^2 omega^7 on 0 <= omega <= theta(u) (re_quadraticForm_sourceMatrix_le_of_mem_oddBoundaryFlat, sourceAtomRealEnergy_le_of_le_oddEndpointAngle)"),
    83: ("Spectral-gap-controlled sign aperture", "M46", "PROVED_MERGED", "(#285)"),
    84: ("Favorable recent prime-power source terms", "M49", "PROVED_THIS_PR", "near-edge prime terms inside theta_* are >= (pi^6/90) beta_q (delta/(c|H(v)|))^2 omega_q^7 (sourceAtomRealEnergy_index_le_of_contactAngle, primeTerm_ge_of_contactAngle_four); older primes not addressed"),
    85: ("K2 odd source sign via sine convolution", "M47", "PROVED_MERGED", "(#285)"),
    86: ("K2 source sign across early prime samples", "M48", "PROVED_MERGED", "source side (#285)"),
    87: ("K2 source sign through three quarters", "M47", "PROVED_MERGED", "(#285)"),
    88: ("K2 favorable prime terms through log16", "M48", "PROVED_MERGED", "source side (#285)"),
    89: ("Improved centered-index mass coercivity", "M46/M73", "PROVED_THIS_PR", "constant 4 (was C_K < 5)"),
    90: ("Contact fourth-moment gap bounds", "M46/M73", "PROVED_THIS_PR", "parityGap_mul_norm_sq_le_four_mul_source_mul_momentFour"),
    91: ("Older-prime compensating budget", "M50", "OPEN", ""),
    92: ("Remaining contact-conditioned obstruction", "M51", "OPEN", ""),
    93: ("Regularized canonical finite-part energy", "M52/M53", "PROVED_THIS_PR", "energy identity PROVED (#285); its first and second aperture derivatives PROVED_THIS_PR at every L > 0"),
    94: ("Numerical moving-aperture F04 regression", "M53", "EXPERIMENTAL_SIGNAL", "matrix-level regression of the F04 identities, prime-free, in prime cells and at seams, to 1.2e-6 (post285_f04_falsifier.py)"),
    95: ("Unweighted source average and sign reversal", "M54", "PROVED_MERGED", "(#285)"),
    96: ("Partial summation / RH-equivalence firewall", "M55", "PROVED_THIS_PR", "(96.1) psi_sub_self_eq_weightedRemainder; transfer bound abs_psi_sub_self_sub_one_le; R = O(x^eps) for all eps stays an RH-strength premise that is never assumed"),
    97: ("Source-moment phase and seventh jet", "M58/M60", "PROVED_THIS_PR", "phase lock via M74; seventh jet PROVED_MERGED"),
    98: ("Exact complete source-moment arithmetic", "M59", "PROVED_MERGED", "existing source-kernel RHS"),
    99: ("Source endpoint and older-prime balance", "M61", "OPEN", ""),
    100: ("Birdfishie branch comparison", "M63", "OPEN", ""),
    101: ("Canonical shared second-variation observable", "M64/M65", "PROVED_THIS_PR", "identified with the production second variation at every L > 0 (fixedSecondEuler of productionContactF04DerivativeAuthority_of_pos)"),
    102: ("Positive prime-free side of local birdfishie", "M42/M66", "PROVED_MERGED", "fixed-vector side (#285); transported to E'' + (2/L)E' this PR (productionContactEulerCurvature_neg)"),
    103: ("First-contact second-variation nonpositive side", "M65/M66", "PROVED_THIS_PR", "complete second physical value = 2<Aw,w> >= 0 at stationary generated contacts (secondPhysicalValue_nonneg); prime-free form -(2 pi)^2 Q/L^4"),
    104: ("Restricted two-sided local contradiction", "M66", "PROVED_THIS_PR", "no stationary generated strict-even contact below eps_K (possibly vacuous)"),
    105: ("Moving-aperture differentiation analytic target", "M65", "PROVED_THIS_PR", "every L > 0, seams included"),
    106: ("K2 complete source functional negative control", "M67", "INTERVAL_EVIDENCE", "log3 certificate (#285 CI)"),
    107: ("Proof note status / open F04 obligations", "M69", "SCOPE_CONTROL", ""),
    108: ("Strict positive and negative source excursions", "M70", "PROVED_THIS_PR", "sourceEnergyRe_excursions_of_zeroSum"),
    109: ("Full half-aperture Andreief inertia", "M71", "PROVED_THIS_PR", "exact even/odd carrier inertia for 0 < omega <= 1/2 (CanonicalAndreiefInertia); Arb-certified minor signs as regression"),
    110: ("Source compression spectral flow", "M72", "PARTIAL", "first passage PROVED_THIS_PR; multiplicity DERIVED on paper, formal obligation OPEN"),
    111: ("Actual canonical resolvent-selected kernel", "M74", "PROVED_THIS_PR", "canonical_ker_eq_span_of_contact"),
    112: ("Quantitative source/fourth-moment phase locking", "M74", "PROVED_THIS_PR", "canonical_contact_phase"),
    113: ("Canonical complete arithmetic opposite-side target", "M74/M76", "OPEN", "exact reduction DERIVED; opposite side OPEN"),
    114: ("Birdfishie audit / two-sided proof obligations", "M77", "SCOPE_CONTROL", ""),
    115: ("Sharp centered-index Poincare constant", "M73", "PROVED_THIS_PR", "1/4 bound proved; sharpness EXPERIMENTAL_SIGNAL"),
    116: ("Off-contact Ward residual identity", "M74", "PROVED_THIS_PR", "canonical_ward_identity"),
    117: ("Approximate contact phase-bound", "M74", "PROVED_THIS_PR", "canonical_re_conj_mul_momentFour_pos_of_approx"),
    118: ("Canonical resolvent ray fourth-moment gauge", "M74", "PROVED_THIS_PR", "canonical_momentFour_resolventRay"),
    119: ("Uniform negative source interval via derivative", "M75", "PROVED_THIS_PR", "exists_sourceNegativeWindow"),
    120: ("Mixed-sign individual prime terms at large L", "M75", "PROVED_THIS_PR", "individual summands only"),
}


def step_matrix() -> dict:
    rows = [{"step": n, "topic": t, "package": p, "status": s, "anchor_or_note": a}
            for n, (t, p, s, a) in sorted(STEPS.items())]
    counts: dict[str, int] = {}
    for r in rows:
        counts[r["status"]] = counts.get(r["status"], 0) + 1
    return {
        "schema": "post285.step_status_matrix.v1",
        "terminal_claim": TERMINAL,
        "authority": "REPORTING_ONLY",
        "vocabulary": {
            "PROVED_THIS_PR": "Lean theorem added in this PR; pending exact-head CI",
            "PROVED_MERGED": "Lean theorem already on main (PR #284/#285); see the post-284 ledgers",
            "PARTIAL": "a named part is proved, the rest is open",
            "CONDITIONAL": "proved only under explicit open premises (typically F04)",
            "DERIVED": "paper derivation, not formalized",
            "INTERVAL_EVIDENCE": "outward-rounded numerical enclosure; not a Lean theorem",
            "EXPERIMENTAL_SIGNAL": "floating-point evidence only",
            "OPEN": "no proof",
            "SCOPE_CONTROL": "bookkeeping/firewall step, no mathematical claim",
        },
        "counts": counts,
        "steps": rows,
    }


def workflow_harvest() -> dict:
    raw = json.loads((HERE / "pr285_check_runs.json").read_text(encoding="utf-8"))
    runs = [{"job": j, "check_run_id": c, "workflow_run_id": w, "conclusion": k}
            for j, c, w, k in raw["check_runs"]]
    return {
        "schema": "post285.workflow_harvest.v1",
        "authority": "REPORTING_ONLY",
        "subject": {"pr": raw["pr"], "checked_head": raw["head"],
                    "merge_commit": raw["merge_commit"], "source": raw["harvested"]},
        "totals": {"check_runs": len(runs),
                   "distinct_workflow_runs": len({r["workflow_run_id"] for r in runs}),
                   "success": sum(r["conclusion"] == "success" for r in runs)},
        "python_rhrc": next(r for r in runs if r["job"] == "python-rhrc"),
        "note": "Green means workflow correctness only. CI runs on pull_request and workflow_dispatch, not on main pushes, so this exact-head PR receipt is the authority for #285.",
        "check_runs": runs,
    }


DISPOSITIONS = [
    {"id": "X285_M74_RANDOM", "script": "post285_m74_secular_falsifier.py", "package": "M74_RANDOM_OFF_CONTACT",
     "disposition": "EXACT_IDENTITY_REGRESSION_PASS",
     "summary": "rank-one, ray, relative determinant, gamma real > 0, gauge, Ward, approximate bound on 200 random complex instances with non-unitary D"},
    {"id": "X285_M74_CONTACT", "script": "post285_m74_secular_falsifier.py", "package": "M74_CONTACT_PHASE",
     "disposition": "EXACT_IDENTITY_REGRESSION_PASS", "summary": "forced H(x)=1: kernel dimension 1 and Re(conj(Hz)<g,Dz>) = gamma|Hz|^2"},
    {"id": "X285_M74_CONTROLS", "script": "post285_m74_secular_falsifier.py", "package": "M74_CONVENTION_CONTROLS",
     "disposition": "NEGATIVE_CONTROL_FAILS_AS_EXPECTED", "summary": "bilinear pairing breaks Ward; D* in place of D^-1 breaks the ray"},
    {"id": "X285_M30_UNDER_M74", "script": "post285_m74_secular_falsifier.py", "package": "M30_CROSSING_UNDER_M74",
     "disposition": "COUNTERMODEL_SURVIVES_M74_IDENTITIES", "summary": "2x2 crossing satisfies every M74 identity yet A(s) has a negative eigenvalue for s > 0: the secular algebra alone cannot exclude a crossing"},
    {"id": "X285_M70", "script": "post285_gate_a_d_falsifier.py", "package": "M70_SOURCE_EXCURSION",
     "disposition": "EXACT_THEOREM_REGRESSION_PASS", "summary": "min/max of pi^2 e/|z|^2 beyond -1/+1; control without zero sum gives e = 0"},
    {"id": "X285_M73", "script": "post285_gate_a_d_falsifier.py", "package": "M73_QUARTER_POINCARE",
     "disposition": "EXACT_THEOREM_REGRESSION_PASS", "summary": "telescoped mass exact; optimal constant decreasing to 1/4 (signal); 1/4 + 0.01 fails at K = 80"},
    {"id": "X285_M75", "script": "post285_gate_a_d_falsifier.py", "package": "M75_NEGATIVE_WINDOW",
     "disposition": "EXACT_THEOREM_REGRESSION_PASS", "summary": "entry derivative <= 2 + 4 pi K; window inside (0,1) and below -|z|^2/(2 pi^2); true negative run >= ~198 x 2 eta (eta is crude)"},
    {"id": "X285_M76_SECULAR_MARGIN", "script": "post285_m76_secular_margin.py", "package": "M76_SECULAR_MARGIN",
     "disposition": "EXPERIMENTAL_SIGNAL",
     "summary": "actual canonical float matrices, K = 2..5, L = 0.25..6: rank-one relation B D - D A = g H holds to 2e-15 (consistent with the Lean theorem); on the 46 float-resolved (K, L) points B > 0, A > 0 and the secular margin 1 - T(L) > 0 (min 4.4e-4 at K = 3, L = 2.75), with det A / det B = 1 - T to 3e-9; the pole and prime channel contributions to T cancel to relative size up to 7e9; CanonicalShiftedSecular regressions on the same matrices: T(a) = 1 to 3e-9 and the shifted overlap identity to 5e-8 at all 46 resolved even roots below the odd floor, and the odd-first determinant identity det B / det A = 1 + H(A^-1 D^-1 g) to 5e-8 relative",
     "caveat": "50 grid points are below float64 resolution (lambda_min < 1e-10 x matrix scale) and are reported as unresolved, not as signs; no certified enclosure"},
    {"id": "X285_F04_IDENTITY", "script": "post285_f04_falsifier.py", "package": "F04_PRIME_FREE_CELLS_SEAMS",
     "disposition": "EXACT_THEOREM_REGRESSION_PASS",
     "summary": "on the even boundary-flat carrier, K = 2..5, at L = 0.08..0.62 (prime-free), 0.9, 1.3, 1.5 (prime cells) and exactly at the seams log 3, log 4, log 5: the first identity to 5e-8 and the Euler identity to 1.2e-6 relative (5-point finite differences of the executable canonical matrix against Gauss-Legendre quadrature plus the exact prime sum)"},
    {"id": "X285_F04_CONTROLS", "script": "post285_f04_falsifier.py", "package": "F04_CONVENTION_CONTROLS",
     "disposition": "NEGATIVE_CONTROL_FAILS_AS_EXPECTED",
     "summary": "a vector with nonzero coefficient sum misses the Euler identity by the predicted boundary term e'_z(0)(W(L) - rho(L))/L (2.0753 observed vs 2.0753 predicted); adding cCorrection twice misses the first identity by 2 cCorrectionIntegrand(L)|z|^2 (0.44946 vs 0.44946)"},
    {"id": "X285_M66_BOUND", "script": "post285_f04_falsifier.py", "package": "M66_EULER_BOUND",
     "disposition": "EXACT_THEOREM_REGRESSION_PASS",
     "summary": "lambda_max of the Euler form below the Q-NEG-EULER bound at L = 0.25, 0.5, 0.9 eps_K for K = 2..5"},
    {"id": "X285_M66_SIGNALS", "script": "post285_f04_falsifier.py", "package": "M66_RADIUS_AND_GROUND",
     "disposition": "EXPERIMENTAL_SIGNAL",
     "summary": "the Euler form is negative definite on the even carrier up to L = 0.553 (K = 2), 0.425 (3), 0.379 (4), 0.355 (5), and about 0.30 at K = 16; the even ground stays positive on the whole prime-free window for K = 2..16 (minimum 0.096 at K = 2 down to 0.003 at K = 16, always at the right end), so no even contact is seen below log 2",
     "caveat": "floating point grids, no certified enclosure; the ground signal suggests M66 is vacuous for small K"},
    {"id": "X285_M55_IDENTITY", "script": "post285_m55_abel_falsifier.py", "package": "M55_PARTIAL_SUMMATION",
     "disposition": "EXACT_THEOREM_REGRESSION_PASS",
     "summary": "(96.1) at 79997 points x in [1, 20000] (all integers plus three interior points per cell) to 4e-11 relative, with the integral of the step function evaluated exactly cell by cell; psi(1) - 1 = -1 and R(1) = -2; the transfer bound holds with worst ratio 0.5; left limits on both sides also satisfy the identity"},
    {"id": "X285_M55_CONTROL", "script": "post285_m55_abel_falsifier.py", "package": "M55_CONVENTION_CONTROL",
     "disposition": "NEGATIVE_CONTROL_FAILS_AS_EXPECTED",
     "summary": "mixing conventions (psi(n-) against R(n)) misses by exactly Lambda(n) at integers"},
    {"id": "X285_M38_EXTREMA", "script": "post285_m55_abel_falsifier.py", "package": "M38_REMAINDER_EXTREMA",
     "disposition": "EXACT_THEOREM_REGRESSION_PASS",
     "summary": "finite sup and inf formulas agree with dense sampling for X just below, at and just after 2, 3, 4, 5, 8, 9, 16, 25, 27, 32, 49, 97, 128, 500; control: dropping the cut min(m+1, X) undershoots the infimum at non-integer X"},
    {"id": "X285_M71_SIGNS", "script": "post285_m71_andreief_falsifier.py", "package": "M71_SIGNED_MINORS",
     "disposition": "EXACT_THEOREM_REGRESSION_PASS",
     "summary": "Arb-certified leading-minor signs of the even and odd carrier Gram matrices for K = 2..9 at 14 apertures omega in [1/1000, 1/2] (224 cells, 512-bit balls, none unresolved) match (-1)^{r(r-1)/2} and (-1)^{r(r+1)/2}; Jacobi counts equal the proved inertia; mpmath eigenvalue inertia agrees for K = 2..7 at omega = 1/20, 1/5, 1/3, 1/2; carrier Gram entries equal the Andreief convolution integrals to 1e-40"},
    {"id": "X285_M71_CONTROLS", "script": "post285_m71_andreief_falsifier.py", "package": "M71_APERTURE_CONTROLS",
     "disposition": "NEGATIVE_CONTROL_FAILS_AS_EXPECTED",
     "summary": "beyond the half aperture certified minor signs break the pattern (e.g. K = 3 at omega = 4/5 and 9/10), and at a = 3 pi/2 a pair factor is positive: the hypothesis omega <= 1/2 is not removable"},
    {"id": "X285_M27_SLOPES", "script": "post285_m27_root_slope_falsifier.py", "package": "M27_ALTERNATING_ROOT_SLOPES",
     "disposition": "EXACT_THEOREM_REGRESSION_PASS",
     "summary": "on the float canonical operator (K = 2..5, L = 0.5..6 step 0.5) the resolvent derivative H(D^-1 (B - a)^-2 g) matches the product formula at all 22 resolved even roots below the odd floor (relative residual < 1e-8), a central difference agrees (< 2e-5), the sign rule holds at every root and 1 - T equals the eigenvalue-product ratio to 4e-15. At most one even root lies below the odd floor on this grid, so only the first (+) slope is exercised numerically."},
    {"id": "X285_M27_CONTROLS", "script": "post285_m27_root_slope_falsifier.py", "package": "M27_CONTROLS",
     "disposition": "NEGATIVE_CONTROL_FAILS_AS_EXPECTED",
     "summary": "C1: perturbing B_L off the rank-one relation breaks the product formula (relative residual up to 4.6e8); C2: the decreasing-order sign rule (-1)^{#{i : a_i > a_j}} fails at 7 roots, so the increasing count is the right convention"},
    {"id": "X285_M08_CUBIC_SCHUR", "script": "post285_m08_cubic_schur_falsifier.py", "package": "M08_ABSTRACT_CUBIC_SCHUR",
     "disposition": "EXACT_THEOREM_REGRESSION_PASS",
     "summary": "exact SymPy third Taylor coefficient of s = a - b* H^-1 b equals the general, symmetric and response forms on 18 seeded families: real symmetric of complement dimension 1..4 (dimension 1 is the 2x2 Schur toy model) and complex Hermitian of dimension 1..2 with the real-part form"},
    {"id": "X285_M08_CONTROLS", "script": "post285_m08_cubic_schur_falsifier.py", "package": "M08_CONTROLS",
     "disposition": "NEGATIVE_CONTROL_FAILS_AS_EXPECTED",
     "summary": "C1: coefficient 3 instead of 6 on <b', R H' R b'> fails on all 18 families; C2: b(t0) != 0 breaks the formula on all 12 real families; C3: with s = s' = s'' = 0 at t0, s''' = 1 gives s > 0 and s''' = -1 gives s < 0 just to the right, matching the necessary sign"},
    {"id": "X285_M09_IDENTITY", "script": "post285_m09_weighted_remainder_falsifier.py", "package": "M09_ZERO_ENDPOINT_WEIGHTED_REMAINDER",
     "disposition": "EXACT_THEOREM_REGRESSION_PASS",
     "summary": "at 30 digits the direct pole/arch/prime value A_L[h] equals int R(e^t) h' + int (e^{-t/2} - rho) h on 50 cases (relative residual < 1e-28): complex polynomial tests t(L - t)p(t) and the contact form t^2 e(1 - t/L) with the Lean derivative, at ten apertures including L < log 2, the seam log 2 and points just past log 4 and log 7"},
    {"id": "X285_M09_CONTROLS", "script": "post285_m09_weighted_remainder_falsifier.py", "package": "M09_CONTROLS",
     "disposition": "NEGATIVE_CONTROL_FAILS_AS_EXPECTED",
     "summary": "C1: h(L) != 0 misses by exactly R(e^L) h(L); C2: dropping the main term 2 sqrt x misses by exactly -int e^{t/2} h; C3: dropping the chain-rule factor -1/L in the contact derivative gives a nonzero miss"},
    {"id": "X285_M45_BOUND", "script": "post285_m45_odd_endpoint_falsifier.py", "package": "M45_ODD_ENDPOINT_QUANTITATIVE",
     "disposition": "EXACT_THEOREM_REGRESSION_PASS",
     "summary": "Arb (256-bit) certifies -Re e_u(omega) - (pi^6/90) |M_3|^2 omega^7 > 0 at 232 cells: 29 Gaussian-integer legal odd vectors (K = 2..8, including the K = 2 generator) at eight rational apertures up to the B-angle, the aperture hypothesis itself certified; minimum ratio 1.996. At 40 digits the sine Taylor bound, the remainder bound |T_u + M_3 t^3/6| <= B |t|^5/120, the beta integral a^7/140 and B <= A_K ||u|| hold; the ratio tends to 16/7 as omega -> 0, so pi^6/90 is sharp up to the 7/16 product factor"},
    {"id": "X285_M45_CONTROLS", "script": "post285_m45_odd_endpoint_falsifier.py", "package": "M45_CONTROLS",
     "disposition": "NEGATIVE_CONTROL_FAILS_AS_EXPECTED",
     "summary": "C1: the constant (16/7)(1 + 1e-3) pi^6/90 fails at omega = 1e-4; C2: without the aperture restriction the K = 2 generator has e(1) = 20 > 0 (certified); C3: dropping oddness (adding an even part with M_2 = 4, keeping M_1 = 0 and M_3 = 12) makes Re e > 0 at small omega; C4: with M_3 = 0 (K = 3 fifth-moment witness) -e/omega^7 -> 0, so no positive omega^7 bound exists without m > 0"},
    {"id": "X285_M49_NEAR_EDGE_PROBE", "script": "post285_m49_near_edge_probe.py", "package": "M49_NEAR_EDGE_PRIME_BENEFIT",
     "disposition": "EXPERIMENTAL_SIGNAL",
     "summary": "float canonical matrices, K = 2..6, L = 0.25..6 step 0.25, even ground state (not a contact): the parity-gap input holds to float rounding and all 329 near-edge sample checks of the proved chain pass (energies at 50 digits). theta_* (c = 4) is 0.084 for K = 2, at most 0.052 for K = 3, 0.037 for K = 4, 0.028 for K = 5 and 0.022 for K = 6. Prime samples fall inside theta_* in 20 of 24 K = 2 rows and 6 of 24 K = 3 rows, and in none for K = 4..6 on this grid: the near-edge benefit is vacuous there. 12 rows have parity gap 0 to float resolution and are skipped"},
    {"id": "X285_M12_STEP28_CERTIFIED", "script": "post285_m09_weighted_remainder_falsifier.py", "package": "M12_STEP28_REPLAY",
     "disposition": "CERTIFIED_DISCOVERY_REPLAY",
     "summary": "the historical Step 28 float values are now Arb-certified at K = 2, L = 1.2, z = (1,-4,6,-4,1), Dz = (-2,4,0,-4,2): E(Dz) in [0.2154944559 +/- 4e-11] > 0 (M05 regularized value) and A_L[t^2 e_{Dz}(1 - t/L)] in [-0.52241962817044517287 +/- 2e-21] < 0; both historical 8-digit values lie within 5e-9. z is not an actual contact: this certifies only that positive ordinary odd energy does not force a positive weighted value (gate G-WEIGHTED). Supersedes the post-284 X12_HISTORICAL_STEP28 status UNKNOWN_NOT_REPLAYED"},
]


def experiment_dispositions() -> dict:
    return {"schema": "post285.experiment_dispositions.v1", "terminal_claim": TERMINAL,
            "authority": "EXPERIMENTAL/REGRESSION ONLY",
            "scripts_dir": "research/RHRC/routes/R003_ccm_bridge/post285",
            "experiments": DISPOSITIONS}


PRODUCTS = {
    "PROOF_ROOTS.json": proof_roots,
    "OPEN_OBLIGATIONS.json": open_obligations,
    "STEP_STATUS_MATRIX.json": step_matrix,
    "WORKFLOW_HARVEST.json": workflow_harvest,
    "EXPERIMENT_DISPOSITIONS.json": experiment_dispositions,
}


def render(fn) -> str:
    return json.dumps(fn(), indent=2, ensure_ascii=False) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser()
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--write", action="store_true")
    g.add_argument("--check", action="store_true")
    args = ap.parse_args()
    assert sorted(STEPS) == list(range(18, 121)), "step matrix must cover 18..120"
    stale = []
    for name, fn in PRODUCTS.items():
        text = render(fn)
        path = HERE / name
        if args.write:
            path.write_text(text, encoding="utf-8")
        elif not path.is_file() or path.read_text(encoding="utf-8") != text:
            stale.append(name)
    if stale:
        print("POST285 LEDGERS: STALE " + ", ".join(stale))
        return 1
    print("POST285 LEDGERS: " + ("WRITTEN" if args.write else "CURRENT"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
