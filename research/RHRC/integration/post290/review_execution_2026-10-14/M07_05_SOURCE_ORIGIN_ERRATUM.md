# M07.05 — Compiler declaration-origin erratum

Date: 2026-10-15
Scope: PR #292, `research/post290-step123-output`
Claim status: **RH OPEN**.

## Exact correction

The public declaration `Zeta23.CCM.poleNeutralIndexEquiv` is **defined**
in `Zeta23/CCM/CanonicalPoleNeutralGeometry.lean` (definition at source line 163
in the reviewed historical head `16d67bad0c6ba8065eb2ee7f151ffc2c102aab58`).

`Zeta23/CCM/CanonicalPoleNeutralCarrier.lean` *imports* that module; it
is not the defining module. The frozen `spec/API_CROSSWALK.json` and companion
`spec/API_CROSSWALK.md` recorded Carrier as the origin. This is a
**source-origin inventory error**, not a changed mathematical definition.

The active compiler binding in `Zeta23/RHRC/Step123OutputBindings.lean`
now points to `Zeta23.CCM.CanonicalPoleNeutralGeometry` and retains the
public declaration name and `DEF` kind. No alias is fabricated and neither
frozen historical crosswalk is modified.

## Proof/claim firewall

The equivalence is the actual restricted centered-index linear equivalence
of even/odd native pole-neutral carriers for `0 < L` and `1 ≤ K`.
It is not asserted to preserve the norm. The separately proved
`poleNeutralIndex_norm_lower` controls its quantitative norm behavior.
The `K < 3` degenerate-carrier case remains governed by its existing results.

This erratum creates **no** new Lean theorem, RH closing-law premise,
or D2 numerical certificate. Exact-head Lean resolver compilation and
all required 99 public export checks remain the acceptance authority.

## Verification

- `test_formal_receipt.py`: verifies the actual registry's corrected
  origin/kind and rejects an importing-module substitution.
- `Step123OutputBindings.lean`: must resolve the exact name, originating
  module, normalized type, and admissible axiom footprint.
- The frozen M07.05 requirement and every other frozen output field persist.
