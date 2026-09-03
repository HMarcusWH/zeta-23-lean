# RHRC formal audit — merged through FIRST-BAD-SPECTRUM / PR #107

> **RH remains OPEN.**

## Current merged authority

~~~text
theorem-state anchor = PR #107 merge b7d1022e33e2177c5597d008f593d3684d0ec720
validated theorem head = cfcf397cc8c15dbb368fbee3a161b8733061b770
validated synthetic merge = 19cd290510fe4fb1d253522c29644ff3e4563c03
validated theorem tree = 719b45162fd0814581759661f12eab16c46e1201
live main = b7d1022e33e2177c5597d008f593d3684d0ec720
theorem-bearing merged through = PR #107
RHRC #717 = SUCCESS
Permansson #490 = SUCCESS
axioms = [propext, Classical.choice, Quot.sound]
sorryAx = absent
date = 2026-09-03
RH = OPEN
~~~

## Exact PR #107 validation

~~~text
base = 26975c00c1ab099aaa03c8179ad8a1c37b129700
final theorem head = cfcf397cc8c15dbb368fbee3a161b8733061b770
synthetic merge tested = 19cd290510fe4fb1d253522c29644ff3e4563c03
merge/main = b7d1022e33e2177c5597d008f593d3684d0ec720
validated/merged theorem tree = 719b45162fd0814581759661f12eab16c46e1201
Lean = 4.33.0-rc2
python RHRC suite = SUCCESS
R003 normalization/source firewall = SUCCESS
CCM build = SUCCESS
ExceptionalZero build = SUCCESS
forbidden-placeholder gate = SUCCESS
Permansson #490 = SUCCESS
~~~

The CI checkout log confirms the Lean job compiled the exact synthetic merge. The merged main
commit has the same theorem tree.

## PR #107 formally validated surface

**PROVED:**
- `parityCompressedCanonicalCLM` / `parityCompressedCanonical`;
- exact compressed/self inner-product bridge;
- `parityCompressedCanonical_isSymmetric`;
- `exists_negative_compressed_direction_of_parityBad`;
- `exists_negative_eigenmode_of_parityBad`;
- `re_inner_successor_nonnegative_on_centeredImage`;
- `negative_eigenmode_not_centeredImage`;
- `exists_firstBadParity_negativeEigenmode_of_offLine_zero` and existential wrapper.

Every printed #107 production theorem depends only on `[propext, Classical.choice, Quot.sound]`;
`sorryAx` is absent.

## Current formal state

~~~text
least bad parity + predecessor nonnegative + 1D shell         PROVED / #105
parity-constrained compression                                PROVED / #107
compressed symmetry/self-form                                 PROVED / #107
negative constrained eigenmode                                PROVED / #107
negative first-bad eigenmode not inherited                    PROVED / #107
off-line zero -> first-bad negative spectral endpoint         PROVED / #107

nonzero shell projection                                      DERIVED / OPEN FORMALIZATION
negative index one / unique negative eigenline                DERIVED / OPEN FORMALIZATION
parity-specific normal-space/KKT                              OPEN
shifted scalar Schur/Feshbach rigidity                        OPEN
RH                                                             OPEN
~~~

## Permanent firewalls

- `v ∉ predecessorImage` does not imply a pure shell vector.
- the one-dimensional shell is not proved invariant.
- D is not unitary and does not automatically transport orthogonal shells.
- use `A - lam I` for `lam < 0`, not `A⁻¹`.
- negative-index-one is derived but not yet theorem-locked.
- no KKT contradiction, positivity theorem, finite-to-infinite theorem or RH theorem exists.

**RH remains OPEN.**
