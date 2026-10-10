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
     "status": "OPEN",
     "detail": "Exact parity inertia for 0 < omega < 1/2 (Andreief signed leading minors, Jacobi/Sylvester signature, polynomial-carrier equivalence) is not formalized. Half-aperture inertia stays PROVED from PR #285; interior inertia has numerical evidence only (no authority)."},
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
     "status": "OPEN",
     "detail": "d_lambda T_L(a_j) = prod_{i != j}(a_i - a_j) / prod_k(b_k - a_j) with sign (-1)^(j-1) is not formalized (needs eigenvalue-product determinant expansions). No lambda-monotonicity and no aperture-derivative sign is claimed."},
    {"id": "M28_CONTACT_OVERLAP_IDENTITY", "package": "M28", "steps": "60",
     "status": "PROVED_PENDING_CI",
     "detail": "canonical_contact_overlap: at an even contact with positive odd bottom, <x_L, D^-1 g> * S_L(D^-1 B_L^-1 B_L^-1 g) = |x_L|^2, so both factors are nonzero, and |x_L| <= |D^-1 g| |S_L(w_L)|. Sign-free."},
    {"id": "M28_OVERLAP_POSITIVITY", "package": "M28", "steps": "60",
     "status": "OPEN",
     "detail": "<x_L, D^-1 g> > 0 (equivalently c* = S_L(w_L) > 0) needs determinant-derivative or first-crossing positivity input; not proved."},
    {"id": "M14_ODD_FIRST_AND_TIED_BRANCH_ALGEBRA", "package": "M14/M77", "steps": "global branch analysis",
     "status": "PROVED_PENDING_CI",
     "detail": "Swapped rank-one instance A D^-1 - D^-1 B = (-D^-1 g) (x) (H o D^-1). With positive even bottom: ker B_L lies on span(D A_L^-1 D^-1 g) (finrank <= 1), B_L singular iff S_L(A_L^-1 D^-1 g) = -1, det B_L = det A_L (1 + S_L(A_L^-1 D^-1 g)). Tied: A_L z = 0 and B_L y = 0 imply S_L(z) <g, y> = 0. Identities only; no branch is excluded."},
    {"id": "M14_BRANCH_EXCLUSION", "package": "M14", "steps": "global branch analysis",
     "status": "OPEN",
     "detail": "No even-first, odd-first, tied, fresh-born or interior branch is excluded. The contact criteria above are equivalent to the contacts themselves."},
    {"id": "M65_PRIME_FREE_F04", "package": "M65", "steps": "101, 103, 105",
     "status": "OPEN",
     "detail": "Prime-free real-aperture differentiation of the exact production compressed family on 0 < L < log 2 (t = Lx substitution, wCorrection derivative, endpoint cancellation) and its identification with the fixed-vector second test are not formalized."},
    {"id": "F04_GLOBAL_PRODUCTION_DERIVATIVE_AUTHORITY", "package": "M06/M53", "steps": "21, 24, 93, 105",
     "status": "OPEN",
     "detail": "Global F04 across prime seams remains OPEN; no theorem in this PR assumes or supplies it."},
    {"id": "M76_ARITHMETIC_COMPOSITION", "package": "M76", "steps": "113, 120",
     "status": "OPEN",
     "detail": "Contact-conditioned opposite-side inequality for the complete source-moment arithmetic remains OPEN. The M75 mixed individual signs exclude termwise prime positivity; they are not an RH contradiction."},
    {"id": "OBS060O_STATIONARY_SATURATION_EXCLUSION", "package": "M13", "steps": "74, 104",
     "status": "OPEN", "detail": "Unchanged by this PR."},
    {"id": "M77_INTEGRATION", "package": "M77", "steps": "107, 114",
     "status": "IN_PROGRESS",
     "detail": "Ledgers, workflow targets, axiom audit and proof-escape receipts for M70-M75, M26-M28 and the branch algebra in this PR; claim-registry binding of the new roots deferred until the #285 cleanup PR (which edits the registry) lands."},
    {"id": "RH", "package": "terminal", "steps": "-", "status": "OPEN", "detail": "RH_OPEN."},
]

POST284_CROSS_REFERENCES = [
    {"post284_id": "M17_GENERAL_OMEGA_ANDREIEF_INERTIA", "effect": "unchanged (OPEN); see M71_INTERIOR_ANDREIEF_INERTIA"},
    {"post284_id": "M18_SPECTRAL_FLOW_PASSAGES", "effect": "first passage proved here (M72_SOURCE_SPECTRAL_FLOW_FIRST_PASSAGE); multiplicity count still OPEN"},
    {"post284_id": "F_M21_PHASE_LOCK", "effect": "canonical contact phase identity proved here (canonical_contact_phase, M74); contact existence and its sign consequences still OPEN"},
    {"post284_id": "F_M58_M63_SOURCE_MOMENT_BIRDFISHIE", "effect": "M58 phase-lock component discharged by M74; M61-M63 OPEN"},
    {"post284_id": "F_M46_COERCIVITY", "effect": "constant improved from C_K < 5 to 4 (M73)"},
    {"post284_id": "F_M53_M65_F04_DERIVATIVES", "effect": "unchanged (OPEN); see M65_PRIME_FREE_F04"},
    {"post284_id": "F04_PRODUCTION_DERIVATIVE_AUTHORITY", "effect": "unchanged (OPEN)"},
    {"post284_id": "F_M27_ALTERNATING_SLOPES", "effect": "canonical shifted secular equation and simple even roots below the odd floor proved here (M26_M27_CANONICAL_SHIFTED_SECULAR); alternating slope formula still OPEN"},
    {"post284_id": "F_M28_RESOLVENT_OVERLAP", "effect": "exact overlap identity proved here (M28_CONTACT_OVERLAP_IDENTITY); positivity still OPEN (M28_OVERLAP_POSITIVITY)"},
    {"post284_id": "M14_OTHER_BRANCHES", "effect": "odd-first and tied branch algebra proved here (M14_ODD_FIRST_AND_TIED_BRANCH_ALGEBRA); no branch excluded"},
]


def open_obligations() -> dict:
    return {
        "schema": "post285.open_obligations.v1",
        "terminal_claim": TERMINAL,
        "authority": "REPORTING_LEDGER",
        "note": "The post-284 ledger is not edited by this PR; promotion of its PR #285 *_PENDING_CI rows belongs to the separate #285 cleanup PR.",
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
    21: ("Production derivative authority interface", "M06", "OPEN", "F04 has no proof constructor"),
    22: ("Physical pole/arch/prime normalization", "M05", "PROVED_MERGED", "CanonicalRegularizedEnergyIdentity (#285)"),
    23: ("Exact finite source and zero-endpoint jets", "M07", "PROVED_MERGED", "source-coordinate jets; operator seam Taylor estimates open"),
    24: ("Aperture derivatives and source transport", "M06", "OPEN", "F04-dependent"),
    25: ("Contact generation from a first bad state", "M00", "PROVED_MERGED", "generated contact frontier"),
    26: ("Contact directional first variation", "M00", "PROVED_MERGED", "production first variation"),
    27: ("F04-weighted contact response reduction", "M09", "CONDITIONAL", "requires F04"),
    28: ("Exploratory sign witnesses and falsification", "M12", "EXPERIMENTAL_SIGNAL", "research only"),
    29: ("Two-scalar stationary curvature identity", "M03", "OPEN", "M03_TWO_SCALAR_CONTACT_TRANSPORT"),
    30: ("Fourier-convolution source identity", "M04", "PROVED_MERGED", "SourceFourierConvolution (#285)"),
    31: ("K=3 exact source counterexample", "M04", "PROVED_MERGED", "SourceSignCountermodels (#285)"),
    32: ("Von Mangoldt discrepancy and weighted balance", "M09", "OPEN", "M09_WEIGHTED_REMAINDER_IDENTITY"),
    33: ("Ninth-order even seam jump", "M10", "OPEN", "M10_NINTH_ORDER_OPTIMIZED_SCHUR_JUMP"),
    34: ("Third derivative Schur and arithmetic bridge", "M08", "OPEN", "M08_ABSTRACT_CUBIC_SCHUR"),
    35: ("Analytic first-crossing seam dichotomy", "M11", "CONDITIONAL", "StrictEvenPrimeSeamDichotomy: premises explicit"),
    36: ("Finite source-moment filtration", "M15", "PROVED_MERGED", "SourceMomentVandermondeFiltration (#285)"),
    37: ("Boundary-flat hierarchy of source moments", "M15", "PROVED_MERGED", "SourceMomentVandermondeFiltration (#285)"),
    38: ("Nonvanishing first source jets", "M15", "PROVED_MERGED", "first-jet signs (#285)"),
    39: ("Moving legal negative/positive source witnesses", "M16", "OPEN", "M16_SMALL_OMEGA_LEGAL_FORM_INDEFINITENESS"),
    40: ("Moving-ray sign countercontrols", "M16", "PROVED_MERGED", "exact controls in SourceSignCountermodels (#285)"),
    41: ("Gap-driven fourth-moment rigidity", "M19", "PROVED_MERGED", "inequality form (ContactNinthJumpGapBound); M73 improves constant"),
    42: ("Higher-moment source signs and limits", "M15/M18", "DERIVED", "not separately formalized"),
    43: ("Parity polynomial reduction", "M17", "PROVED_MERGED", "SourceParityPolynomialCoordinates (#285)"),
    44: ("Andreief signed-minor inertia target", "M17/M71", "PARTIAL", "omega = 1/2 PROVED (#285); 0 < omega < 1/2 OPEN"),
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
    59: ("Spectral root derivative and simplicity", "M27", "PARTIAL", "simplicity PROVED_THIS_PR (canonical_finrank_eigenspace_le_one); alternating root slopes OPEN"),
    60: ("Contact resolvent overlap identity", "M28", "PARTIAL", "exact identity PROVED_THIS_PR (canonical_contact_overlap); positivity OPEN"),
    61: ("Source-resolvent aperture derivative", "M29", "OPEN", ""),
    62: ("Second source-resolvent balance", "M29", "OPEN", ""),
    63: ("Third-order source-resolvent obstruction", "M29", "OPEN", ""),
    64: ("Simplicity of all even roots below odd floor", "M27", "PROVED_THIS_PR", "canonical_finrank_eigenspace_le_one (geometric multiplicity <= 1; A_L symmetric)"),
    65: ("Abstract stationary cubic crossing countermodel", "M30", "PROVED_MERGED", "(#285)"),
    66: ("Differential Gronwall contact barrier", "M31", "OPEN", ""),
    67: ("Full arithmetic derivative inequality target", "M32", "OPEN", ""),
    68: ("Odd source-sign reversal of contact vector", "M33", "OPEN", ""),
    69: ("Physical second-order sign-changing test", "M33/M41", "INTERVAL_EVIDENCE", "M41 interval enclosure (#285)"),
    70: ("Exact archimedean density and remainder", "M34", "OPEN", ""),
    71: ("Stationary arithmetic remainder oscillation", "M34", "OPEN", ""),
    72: ("Weighted elementary source integral", "M35", "PROVED_MERGED", "CanonicalSourceWeightedIntegral (#285)"),
    73: ("Uniform small-aperture physical positivity", "M36", "PROVED_MERGED", "fixed-vector test only (#285)"),
    74: ("Conditional local stationary contact contradiction", "M37", "CONDITIONAL", "F04-conditional"),
    75: ("Finite extrema of logarithmic prime remainder", "M38", "OPEN", ""),
    76: ("Contact sign scope and next arithmetic target", "M39", "OPEN", ""),
    77: ("General negative integrated source operator", "M40", "PROVED_MERGED", "(#285)"),
    78: ("K2 prime-free physical test falsifier", "M41", "INTERVAL_EVIDENCE", "(#285)"),
    79: ("Explicit finite-K initial positive radius", "M42", "PROVED_MERGED", "fixed-vector test (#285)"),
    80: ("K3 indefinite physical second-order test", "M43", "INTERVAL_EVIDENCE", "(#285)"),
    81: ("Entering seventh-order prime second-test sign", "M44", "OPEN", ""),
    82: ("Explicit odd endpoint source Taylor bound", "M45", "OPEN", ""),
    83: ("Spectral-gap-controlled sign aperture", "M46", "PROVED_MERGED", "(#285)"),
    84: ("Favorable recent prime-power source terms", "M49", "OPEN", ""),
    85: ("K2 odd source sign via sine convolution", "M47", "PROVED_MERGED", "(#285)"),
    86: ("K2 source sign across early prime samples", "M48", "PROVED_MERGED", "source side (#285)"),
    87: ("K2 source sign through three quarters", "M47", "PROVED_MERGED", "(#285)"),
    88: ("K2 favorable prime terms through log16", "M48", "PROVED_MERGED", "source side (#285)"),
    89: ("Improved centered-index mass coercivity", "M46/M73", "PROVED_THIS_PR", "constant 4 (was C_K < 5)"),
    90: ("Contact fourth-moment gap bounds", "M46/M73", "PROVED_THIS_PR", "parityGap_mul_norm_sq_le_four_mul_source_mul_momentFour"),
    91: ("Older-prime compensating budget", "M50", "OPEN", ""),
    92: ("Remaining contact-conditioned obstruction", "M51", "OPEN", ""),
    93: ("Regularized canonical finite-part energy", "M52/M53", "PARTIAL", "energy identity PROVED (#285); F04 OPEN"),
    94: ("Numerical moving-aperture F04 regression", "M53", "EXPERIMENTAL_SIGNAL", ""),
    95: ("Unweighted source average and sign reversal", "M54", "PROVED_MERGED", "(#285)"),
    96: ("Partial summation / RH-equivalence firewall", "M55", "OPEN", ""),
    97: ("Source-moment phase and seventh jet", "M58/M60", "PROVED_THIS_PR", "phase lock via M74; seventh jet PROVED_MERGED"),
    98: ("Exact complete source-moment arithmetic", "M59", "PROVED_MERGED", "existing source-kernel RHS"),
    99: ("Source endpoint and older-prime balance", "M61", "OPEN", ""),
    100: ("Birdfishie branch comparison", "M63", "OPEN", ""),
    101: ("Canonical shared second-variation observable", "M64/M65", "OPEN", "identification with production second variation OPEN"),
    102: ("Positive prime-free side of local birdfishie", "M42/M66", "PROVED_MERGED", "fixed-vector side (#285)"),
    103: ("First-contact second-variation nonpositive side", "M65", "OPEN", "prime-free F04"),
    104: ("Restricted two-sided local contradiction", "M66", "CONDITIONAL", ""),
    105: ("Moving-aperture differentiation analytic target", "M65", "OPEN", ""),
    106: ("K2 complete source functional negative control", "M67", "INTERVAL_EVIDENCE", "log3 certificate (#285 CI)"),
    107: ("Proof note status / open F04 obligations", "M69", "SCOPE_CONTROL", ""),
    108: ("Strict positive and negative source excursions", "M70", "PROVED_THIS_PR", "sourceEnergyRe_excursions_of_zeroSum"),
    109: ("Full half-aperture Andreief inertia", "M71", "OPEN", "interior 0 < omega < 1/2 not formalized; numerical evidence only"),
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
