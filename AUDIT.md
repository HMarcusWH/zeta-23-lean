# RHRC formal audit — merged through N-FLOW / PR #100

> **RH remains OPEN.**

## Current merged authority

~~~text
theorem-state anchor = PR #100 merge 4427e2a8c8d90dbb7d66d9d96f9a410cecb75df9
validated theorem head = 497adcd6a746d49fd23654cabf4ed8f0c58db8a9
theorem tree = 705ab8b88728a5b90d850eb4b51c01a66811f088
theorem-bearing merged through = PR #100
live GitHub main = authoritative
date = 2026-09-02
~~~

## Exact PR #100 validation

~~~text
base = c37b701ef3e78b0446b82c4c606d5f64bc9245bd
final head = 497adcd6a746d49fd23654cabf4ed8f0c58db8a9
head tree = 705ab8b88728a5b90d850eb4b51c01a66811f088
merge = 4427e2a8c8d90dbb7d66d9d96f9a410cecb75df9
merge tree = 705ab8b88728a5b90d850eb4b51c01a66811f088
RHRC #691 = SUCCESS
Permansson #464 = SUCCESS
CCM build = SUCCESS
ExceptionalZero build = SUCCESS
forbidden-placeholder gate = SUCCESS
axioms = [propext, Classical.choice, Quot.sound]
sorryAx = absent
~~~

The exact theorem tree validated at the final head is the merged main tree. No Codex review was available because the code-review usage limit was reached; that is not a Lean/CI proof gate.

## Current formal theorem state

~~~text
F1 canonical finite negative obstruction              PROVED
K0-F1 constrained algebra / Hermitianity              PROVED
K0-F1 exact one-channel displacement                  PROVED
K0-F1E exact rank / finrank 2*N-2                     PROVED
K0-F1E N>=2 floor                                     PROVED
K0-F1E Euclidean constrained sector                   PROVED
K0-F1E canonical Euclidean symmetry                   PROVED
K0-F1E quadraticForm / inner-self bridge              PROVED
K0-F1E Euclidean constrained negative direction       PROVED
N-FLOW exact centered principal-block nesting         PROVED
N-FLOW every centered moment preserved                PROVED
N-FLOW Euclidean isometric constrained extension      PROVED
N-FLOW fixed-L persistent negative tail               PROVED

reversal/parity                                       OPEN / NEXT
global first-bad-N / 2D shell theorem                 DERIVED / OPEN FORMALIZATION
compressed negative constrained eigenmode             OPEN
first-bad parity / 1D-shell impossibility              OPEN
RH                                                    OPEN
~~~

## OBS-017 after #100

Closed:

~~~text
coordinate transport
Euclidean constrained subspace
quadraticForm / inner-self identity
Euclidean centered zero-extension isometry
constrained membership preservation under N extension
canonical quadratic-value preservation under N extension
~~~

Open:

~~~text
orthogonal compression to the constrained subtype
finite-dimensional constrained Rayleigh/eigenmode extraction
~~~

The raw #96 norm-one theorem remains semantically distinct from Euclidean norm normalization.

## Post-#100 structural consequence

For fixed L, #100 makes existence of a negative constrained direction upward persistent in N. Together with #98's exact finrank formula this yields, at the mathematical consequence level:

~~~text
nonempty bad-size set -> least global bad N*
dim V_(N+1) - dim V_N = 2
~~~

These consequences are not yet separately theorem-locked as project declarations. Parity is still required before claiming a one-dimensional new shell in either parity sector.

## Promoted-binding hardening

R003_PROMOTED_BINDINGS.json and promoted_binding_lint.py require every PROVED_UNCONDITIONAL R003 theorem claim to agree exactly across the claim registry, promoted binding manifest, #check, and #print axioms surfaces.

PR #100 adds three promoted R003 production bindings for exact centered finite nesting, Euclidean constrained nesting, and the nested Euclidean negative obstruction.

Promotion intent still has to be declared; the lint does not pretend every support #check is an individual claim.

## Permanent firewalls

1. RH remains OPEN.
2. canonicalSourceMatrix is sign-authoritative; finiteMatrix is legacy printed normalization.
3. OBS-015 remains binding.
4. DR-010 remains falsified.
5. low displacement rank alone does not imply positivity or RH.
6. exact finite-N nesting is structural infrastructure; its RH value comes from later first-failure rigidity.
7. principal-block nesting does not imply full operator intertwining or compressed-operator nesting.
8. #100 proves finite nesting, not finite-to-infinite convergence.

**RH remains OPEN.**
