# RHRC formal audit — merged through PARITY-BAD / PR #105

> **RH remains OPEN.**

## Current merged authority

~~~text
theorem-state anchor = PR #105 merge 5e19483c905c07cfe9fef0a97f834004e77b5fb9
validated theorem head = 100fb03cccd44d1c09dadfc41cd104ba753308ee
validated synthetic merge = 4411f6a5a5c679795e043968db70f44922c2a468
theorem tree = 84ed44aaf5ff014a9352901ff1a1a31a29809b6e
theorem-bearing merged through = PR #105
RHRC #706 = SUCCESS
Permansson #479 = SUCCESS
axioms = [propext, Classical.choice, Quot.sound]
sorryAx = absent
date = 2026-09-03
RH = OPEN
~~~

## Exact PR #105 validation

~~~text
base = 08cabfbdd1707760f8b4457fc34db7a149c0d244
final head = 100fb03cccd44d1c09dadfc41cd104ba753308ee
synthetic merge tested = 4411f6a5a5c679795e043968db70f44922c2a468
merge/main = 5e19483c905c07cfe9fef0a97f834004e77b5fb9
validated/merged tree = 84ed44aaf5ff014a9352901ff1a1a31a29809b6e
Lean = 4.33.0-rc2
python RHRC suite = SUCCESS
R003 normalization/source firewall = SUCCESS
CCM build = SUCCESS
ExceptionalZero build = SUCCESS
forbidden-placeholder gate = SUCCESS
Permansson #479 = SUCCESS
~~~

## PR #105 formally validated surface

**PROVED:**

- `indexMatrix_mulVec_centeredZeroExtend`: exact (D_M E=E D_N) on all raw coefficient vectors.
- `quadraticForm_canonicalSourceMatrix_reverseCoefficients`.
- `quadraticForm_evenPart_add_oddPart`: exact parity energy split.
- `parityBad_even_or_odd_of_negative`.
- `two_le_of_parityBad`.
- `parityBad_persists_of_le`.
- `exists_least_parityBad`.
- `nonnegative_of_lt_least_parityBad`.
- `euclidean_nonnegative_of_lt_least_parityBad`.
- `finrank_euclideanParitySuccShell = 1`.
- fixed-aperture fixed-parity bad tail from an off-line zero.
- least-bad parity / predecessor-nonnegative / 1D-shell endpoint from an off-line zero.

Every printed #105 theorem depends only on `[propext, Classical.choice, Quot.sound]`.

## Current formal state

~~~text
fixed-L negative constrained tail                              PROVED / #100
parity symmetry / even commutator collapse                    PROVED / #102
direct parity decomposition / D-equivalence                   PROVED / #103
D / N-flow compatibility                                      PROVED / #105
quadratic parity splitting                                    PROVED / #105
fixed bad parity tail                                         PROVED / #105
least bad parity size >=2                                     PROVED / #105
predecessor parity nonnegative                                PROVED / #105
1D Euclidean successor parity shell                           PROVED / #105

parity-constrained compression                                OPEN
negative constrained eigenmode                                OPEN
unique first-bad negative eigenline                           DERIVED / OPEN FORMALIZATION
parity-specific normal-space/KKT                              OPEN
scalar Schur/Feshbach rigidity                                OPEN
RH                                                             OPEN
~~~

## Permanent firewalls

Repository presence is not compiler validation; #105 is the successful escape from the #103 staged-module example. D is not unitary. Orthogonal shell transport is not proved. One-dimensional shell growth alone does not rule out a first negative eigenvalue. RH remains OPEN.
