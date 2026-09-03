# RHRC formal audit — merged through PARITY-FLOW geometry / PR #103

> **RH remains OPEN.**

## Current merged authority

~~~text
theorem-state anchor = PR #103 merge c7129b1856ea03cdf8b831ae1424140f8a7d90a9
validated theorem head = af43242f55536a8170bf303b9c9558c6a0fccdcf
validated synthetic merge = 16c5ebaa6d6d7e14df853e9a0771ab5ef3b07aba
theorem tree = 56d082947fac6eb4666d0e0666e2c8bcd3c0a7e8
theorem-bearing merged through = PR #103
live GitHub main = authoritative
date = 2026-09-03
~~~

## Exact PR #103 validation

~~~text
base = a434737c088ad2651491f0131b6dd6794c129f4c
final head = af43242f55536a8170bf303b9c9558c6a0fccdcf
synthetic merge tested = 16c5ebaa6d6d7e14df853e9a0771ab5ef3b07aba
merge/main = c7129b1856ea03cdf8b831ae1424140f8a7d90a9
validated/merged tree = 56d082947fac6eb4666d0e0666e2c8bcd3c0a7e8
Lean = 4.33.0-rc2
RHRC #704 = SUCCESS
Permansson #477 = SUCCESS
python RHRC claim/regression suite = SUCCESS
R003 normalization/source firewall = SUCCESS
CCM build = SUCCESS
ExceptionalZero build = SUCCESS
forbidden-placeholder gate = SUCCESS
production axiom surface = [propext, Classical.choice, Quot.sound]
sorryAx = absent
~~~

The workflow explicitly checked out the synthetic merge above. The tree that passed is the tree now merged on main.

## PR #102 validated parity chassis

PR #102 final head `e765147092f1cac533f16dc562f01e0ced647217` and merge `a434737c088ad2651491f0131b6dd6794c129f4c` share theorem tree `38a66adcdd3e3e7d228deacb526dca470989f87e`. RHRC #698 and Permansson #471 succeeded.

Production-support declarations:

~~~text
centeredIndex_rev
centeredEmbedding_rev
centeredMoment_reverseCoefficients
canonicalSourceMatrix_apply_rev_rev
displacementVector_rev
canonicalSourceMatrix_mulVec_reverseCoefficients
displacementPairing_eq_zero_of_even
canonicalSourceMatrix_displacement_mulVec_even_boundaryFlat
~~~

**PROVED:** exact reversal/moment/matrix symmetry and exact canonical commutator collapse on even boundary-flat vectors.

## PR #103 validated parity geometry

The compiler-tested module is `Zeta23/CCM/ConstrainedParityGeometry.lean`.

Production-support declarations:

~~~text
evenBoundaryFlatSubspace_inf_oddBoundaryFlatSubspace
evenBoundaryFlatSubspace_sup_oddBoundaryFlatSubspace
evenToOddIndexLinearMap_injective
evenToOddIndexLinearMap_surjective
evenOddBoundaryFlatLinearEquiv
finrank_evenBoundaryFlatSubspace
finrank_oddBoundaryFlatSubspace
finrank_euclideanEvenBoundaryFlatSubspace
finrank_euclideanOddBoundaryFlatSubspace
euclideanCenteredZeroExtend_mem_euclideanEvenBoundaryFlatSubspace
euclideanCenteredZeroExtend_mem_euclideanOddBoundaryFlatSubspace
~~~

**PROVED:**

~~~text
V_N = V_N^+ direct-sum V_N^-
D : V_N^+ ≃ₗ[ℂ] V_N^-
finrank V_N^+ = N-1
finrank V_N^- = N-1
Euclidean parity sectors have the same dimensions
centered Euclidean N-flow preserves each parity sector.
~~~

The proof of the linear equivalence is stronger than a dimension count: moment zero removes D's central kernel and an explicit odd primitive proves surjectivity.

## Merged source that is NOT theorem authority

`Zeta23/CCM/ParityBadness.lean` was added by PR #103 but is not imported by `Zeta23.CCM.lean`. The #103 `lake build Zeta23.CCM` therefore did not elaborate it.

These declarations are **STAGED / NOT PROVED**:

~~~text
ParityBad
parityBad_persists_of_le
exists_least_parityBad
nonnegative_of_lt_least_parityBad
finrank_euclideanParitySuccShell
~~~

The forbidden-placeholder gate scanned the source; that is not equivalent to compiler validation.

## Current formal theorem state

~~~text
F1 canonical finite negative obstruction                     PROVED
K0-F1 constrained algebra / Hermitianity / displacement      PROVED
K0-F1E exact dimension 2*N-2 + Euclidean sector              PROVED
N-FLOW exact centered nesting / persistent negative tail     PROVED / #100
PARITY reversal/moment/matrix symmetry                       PROVED / #102
PARITY even constrained commutator collapse                  PROVED / #102
PARITY direct constrained decomposition                      PROVED / #103
PARITY D : V+ ≃ₗ V-                                          PROVED / #103
PARITY exact N-1 / N-1 dimensions                            PROVED / #103
PARITY-preserving Euclidean N-flow                           PROVED / #103

global badness upward persistence / least global bad N       DERIVED
negative witness -> negative parity component                DERIVED / OPEN FORMALIZATION
ParityBad machinery / least parity bad / 1D shell            STAGED / NOT PROVED
D / centered-N-flow compatibility                            OPEN
constrained compression / negative constrained eigenmode     OPEN
normal-space / KKT / scalar Schur-Feshbach rigidity          OPEN
RH                                                            OPEN
~~~

## Permanent firewalls

1. RH remains OPEN.
2. canonicalSourceMatrix is sign-authoritative; finiteMatrix is legacy printed normalization.
3. source interface is not source negativity.
4. raw function-space norm is not Euclidean normalization.
5. repository/merge presence is not compiler validation.
6. D-equivalence is algebraic, not unitary.
7. ambient commutator collapse does not imply compressed-operator intertwining.
8. finite nesting is not finite-to-infinite convergence.
9. one-dimensional shell geometry is not itself a contradiction.

**RH remains OPEN.**
