# RHRC formal audit — merged through K0-F1E / PR #98

> **RH remains OPEN.**

## Current merged authority

~~~text
theorem-state anchor = PR #98 merge 4f212e35fefb339646e294573dcb390dae2f6181
theorem tree = 84a678327fffe6806e1e786ac2e159a5ce628f67
theorem-bearing merged through = PR #98
live GitHub main = authoritative
date = 2026-09-02
~~~

## Exact PR #98 validation

~~~text
base = b2e0f4cdbeb7c46afbd5acae0fbad332c334a9ff
final head = 723c63badb2ac787c3dfa78369909477af6bc6a4
head tree = 84a678327fffe6806e1e786ac2e159a5ce628f67
merge = 4f212e35fefb339646e294573dcb390dae2f6181
merge tree = 84a678327fffe6806e1e786ac2e159a5ce628f67
RHRC #685 = SUCCESS
Permansson #458 = SUCCESS
axioms = [propext, Classical.choice, Quot.sound]
sorryAx = absent
~~~

The exact theorem tree validated at the final head is the merged main tree. No Codex review was available because the review usage limit was reached; that is not a Lean/CI proof gate.

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

exact finite-N nesting                                OPEN / NEXT
reversal/parity                                       OPEN / NEXT
compressed negative constrained eigenmode             OPEN
first-bad finite-shell impossibility                  OPEN
RH                                                    OPEN
~~~

## OBS-017 after #98

Closed: coordinate transport, Euclidean constrained subspace, and quadraticForm/inner-self identity.

Open: orthogonal compression and constrained Rayleigh/eigenmode extraction.

The raw #96 norm-one theorem remains semantically distinct from Euclidean norm normalization.

## New control-plane hardening

R003_PROMOTED_BINDINGS.json and promoted_binding_lint.py require every PROVED_UNCONDITIONAL R003 theorem claim to agree exactly across the claim registry, promoted binding manifest, #check, and #print axioms surfaces.

Three older R003 bindings that had #check without #print axioms are repaired in the same PR.

Promotion intent still has to be declared; the lint does not pretend every support #check is an individual claim.

## Permanent firewalls

1. RH remains OPEN.
2. canonicalSourceMatrix is sign-authoritative; finiteMatrix is legacy printed normalization.
3. OBS-015 remains binding.
4. DR-010 remains falsified.
5. low displacement rank alone does not imply positivity or RH.
6. finite-N nesting, if proved, is structural infrastructure; its RH value comes from later first-failure rigidity.

**RH remains OPEN.**
