# HMWH Zeta23 fork — current audit entry point

> **Claim firewall: RH remains OPEN.**

This file records the current high-level validation state. Detailed theorem truth is determined by live GitHub, exact Lean declarations, compiler/CI and the machine registries on the checked ref.

## Authority snapshot

### Current merged baseline

~~~text
main = 879eb6d356d8f62bbe0b9241596b15892498ea64
tree = 9225c993bb9ac680a0f673efc13d191bebc5fd28
merged through = PR #88
RH = OPEN
~~~

### Exact green WCONT-A candidate

~~~text
PR #89 head = 4bcd49e0b8029ac7381c7829a18fefea11f20ba1
base = 879eb6d356d8f62bbe0b9241596b15892498ea64
synthetic merge = 725a562d88a3af654a7050397031cd33b2bcda21
synthetic merge tree = f56b3a200d0ac70df3219a158f6c77c85fc34108
RHRC #619 = SUCCESS
Permansson #392 = SUCCESS
PR state at documentation time = OPEN / NOT MERGED
RH = OPEN
~~~

## Exact #89 validation

The exact WCONT-A head passed:

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

**PROVED / MERGED IN PR #88.**

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
WCONT-A quantitative common-support genuine-W bound          PROVED ON GREEN #89 HEAD
exact diagonal cross-term identity                           PROVED ON GREEN #89 HEAD
quantitative self-form perturbation bound                    PROVED ON GREEN #89 HEAD
F0-B1C WCONT-matched finite approximation                    OPEN / NOW
projection-smallness / moment-residual control               OPEN
strict finite sign transfer                                  OPEN
F1 canonical finite negative obstruction                     OPEN
K0-K3                                                        OPEN
RH                                                           OPEN
~~~

## WCONT-A exact theorem state

Production declarations:

~~~text
Zeta23.norm_paperFT_mul_one_add_normSq_le
Zeta23.ExceptionalZero.zeta_invSqZeroWeight_summable
Zeta23.ExceptionalZero.norm_zeta_Wsummand_le_commonSupport
Zeta23.ExceptionalZero.zeta_W_norm_le_commonSupport
Zeta23.ExceptionalZero.zeta_W_self_sub_self_eq_cross
Zeta23.ExceptionalZero.zeta_W_self_sub_self_norm_le_commonSupport
~~~

All promoted declarations print only

~~~text
[propext, Classical.choice, Quot.sound]
~~~

No sorryAx survives.

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

research/RHRC/routes/R003_ccm_bridge/WCONT_A_POST_GREEN_F0B1C_FRONTIER_2026_09_01.md

**RH remains OPEN.**
