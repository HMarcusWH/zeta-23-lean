# HMWH Zeta23 fork — current audit entry point

> **Claim firewall: RH remains OPEN.**

This file records the current high-level validation state. Detailed theorem truth is determined by live GitHub, exact Lean declarations, compiler/CI and the machine registries on the checked ref.

## Authority snapshot

### Current merged baseline

~~~text
main = 1ad066f0a263725ea7b84447a637fcebda78e9ca
tree = 41f9febd6a02282e746714c2f62407fb51ac8b30
merged through = PR #87
RH = OPEN
~~~

### Exact green F0-B1B candidate

~~~text
PR #88 theorem head = 5e943d8cd6825c3c649198c52d90d1ed5d8d8b47
base = 1ad066f0a263725ea7b84447a637fcebda78e9ca
synthetic merge = 9eb9281394684600b35a58ce2cb3c757d06379cc
synthetic merge tree = d10e7b1e575624ab39fb445297f43168b1867ed1
RHRC #609 = SUCCESS
Permansson #382 = SUCCESS
PR state at documentation time = OPEN / NOT MERGED
RH = OPEN
~~~

## Exact #88 validation

The exact theorem head passed:

- Build CCM formalization;
- Build exceptional-zero foundation;
- reject forbidden placeholders;
- RHRC claim/regression suite;
- cutoff-free normalization lock;
- finite dictionary external-oracle guards;
- source-normalization semantic firewall;
- R004 scalar-shift invariants;
- external-reference dependency guard;
- independent Permansson Lean verification;
- independent placeholder/extra-axiom rejection.

The production declarations print only:

~~~text
[propext, Classical.choice, Quot.sound]
~~~

No sorryAx survives.

## Formal theorem state

### W2-A

**PROVED / REGISTERED.** Concrete-zeta pair W is summability-safe and equals the literature RHS on the exact asymmetric admissible class.

### W0

**PROVED / REGISTERED.** An off-line zero yields one compact C² pole-neutral physical test with strictly negative genuine W self-value.

### W1

**PROVED / REGISTERED.** The negative test can be recentered into a strict interior aperture with L=4r and support inside (r,3r) inside (0,L).

### W2-ZS / direct diagonal W2-C

**PROVED / REGISTERED.**

~~~text
W(h,h)=localizedWeilAdditiveRHS(h,h).
~~~

### Strict negative localized-additive witness

**PROVED / REGISTERED.**

### G1-A

**PROVED / REGISTERED.** The repository additive RHS on finite localized vectors equals the cutoff-free/canonical finite quadratic form.

### F0-B1A — boundary-flat finite Weil restriction

**PROVED / REGISTERED.**

~~~text
moments 0,1,2=0
  -> localizedFiniteVector is global C²
  -> W(v,v)=quadraticForm(canonicalSourceMatrix L N)u.
~~~

Production claim:

~~~text
R003_BOUNDARY_FLAT_FINITE_WEIL_RESTRICTION
~~~

### F0-B1B — exact boundary-flat projection

**PROVED ON EXACT GREEN PR #88 HEAD; NOT YET MERGED AT DOCUMENTATION TIME.**

For N>=1, the exact three-mode correction on centered modes -1,0,+1 cancels centered moments 0,1,2 for arbitrary u.

Lean proves:

~~~text
boundaryFlatProject_boundaryFlat
boundaryFlatProject_eq_self_of_boundaryFlat
boundaryFlatProject_idempotent
~~~

and exact endpoint/moment identities:

~~~text
localizedFiniteFunction_zero_eq_centeredMoment_zero
localizedFiniteFirstJet_zero_eq_centeredMoment_one
localizedFiniteSecondJet_zero_eq_centeredMoment_two
~~~

Registry claim on the #88 branch:

~~~text
R003_BOUNDARY_FLAT_PROJECTION
~~~

The N=0 sector is explicitly outside the construction.

## Current open frontier

~~~text
WCONT-A quantitative common-support genuine-W bound         OPEN / NOW
quadratic W continuity corollary                            OPEN
finite approximation in the selected topology              OPEN
projection-smallness / moment-residual control              OPEN
strict finite sign transfer                                 OPEN
F1 canonical finite negative obstruction                    OPEN
K0-K3                                                       OPEN
RH                                                          OPEN
~~~

## WCONT-A research target

Existing theorem-backed ingredients:

~~~text
Zeta23.WeilEF.zero_sum_inv_sq_gen
Zeta23.WeilEF.EF_zero_sum_summable_gen
Zeta23.ExceptionalZero.zeta_W_literatureRHS_package
~~~

The post-#88 lead is to exploit asymmetric W2-A regularity and seek a common-support estimate of schematic form

~~~text
|W(f,g)|
  <= K_Λ * (||f||_1 + ||f''||_1) * ||g||_1.
~~~

This is **OPEN / LEAD**, not a registered theorem.

## Continuity and projection firewalls

1. Per-approximant summability does not imply a uniform family majorant.
2. The #88 correction by itself need not be boundary-flat and therefore need not be a globally C² hard-window test.
3. The complete projected vector is the legal object.
4. PR #88 does not prove quantitative correction norm bounds.
5. No finite Fourier density theorem is yet load-bearing.
6. Pinned Mathlib does not provide a ready theorem that may simply be cited as “standard Fejer approximation.”

## Normalization firewall

~~~text
canonicalSourceMatrix = cutoffFreeMatrix = sourceEq44Matrix = dictionaryMatrix.
~~~

Historical finiteMatrix remains the printed-normalization object.

## Source-sign firewall

OBS-015 remains binding:

~~~text
source interface is not source negativity.
~~~

G1-B1A finite source transport is proved, but Haar/L²/PsiSharp/QW interface, G1-final, source negativity and G23 remain OPEN.

## Current post-green settlement

research/RHRC/routes/R003_ccm_bridge/F0_B1B_POST_GREEN_WCONT_FRONTIER_2026_09_01.md

**RH remains OPEN.**
