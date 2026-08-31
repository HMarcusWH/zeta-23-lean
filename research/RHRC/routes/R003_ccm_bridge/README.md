# R003 — CCM / finite Weil bridge

Status: **ACTIVE DISCOVERY ROUTE. RH OPEN.**

This README is the living route SSOT for the merged repository. PR-specific settlement files in this directory are historical records; they do not override live Lean/CI or this current route state.

## Objective

Build an exact, source-faithful chain from finite Fourier test functions to the fixed-aperture localized Weil form, and only then use a legitimate variational/core theorem to transport fixed-aperture spectral information.

The critical endpoint is not a finite matrix formula by itself. It is the actual restriction theorem

```text
QW_lambda restricted to E_N = canonicalSourceMatrix.
```

## Current canonical object map

The direct source finite matrix authority is

```text
canonicalSourceMatrix
  = cutoffFreeMatrix
  = sourceEq44Matrix
  = dictionaryMatrix.
```

For positive aperture the existing zero-side bridge also identifies the actual finite zeta zero-side matrix with the cutoff-free/canonical matrix.

The historical printed normalization is

```text
legacyPrintedMatrix = finiteMatrix.
```

with exact scalar-shift relation

```text
canonicalSourceMatrix
  = legacyPrintedMatrix
    + 2*legacyPrintedCorrection(L)*I.
```

No route document may identify `finiteMatrix` directly with ambient `QW_lambda|E_N`.

## Why the normalization firewall exists

The route history matters.

- PR #28 refuted the naïve no-shift CCM/Weil identification and localized the problem to the diagonal archimedean term.
- PR #29 identified the scalar diagonal shift numerically/structurally and proved displacement-transfer algebra.
- PR #33 pinned an independent cutoff-free source oracle.
- PR #65 formalized the cutoff-free matrix and proved its relation to the zero-side/dictionary matrix.
- PR #71 theorem-locked the direct Section-4 equation-(4.4) finite source matrix and exposed the later printed equation-(4.11)/(4.14) normalization inconsistency.
- PR #73 repaired repository semantics: canonical direct-source labels now point to the cutoff-free object; historical printed objects remain frozen.

The lesson is permanent: finite formula agreement does not by itself close source normalization, carrier, measure, functional, and restriction semantics.

## Closed theorem ladder on merged main

### Finite dictionary / explicit-formula layer

Closed work includes:

- finite divided-difference/source calculus;
- finite Guinand--Weil dictionary;
- deterministic dictionary RHS identity;
- literal-tent analytic package;
- mollifier architecture and channel-by-channel limits;
- literal-tent explicit formula;
- exact finite zero-side bridge;
- full real dictionary EF recovery by finite contraction.

### D0 representation layer

Closed classifications include:

- **D0-C:** cutoff-free finite source matrix theorem-locked;
- **D0-R:** generic R002 smooth-taper production object is **SPECIALIZATION_ONLY**, not identical to canonical CCM;
- **D0-B:** Bombieri's zero-index truncation is a different finite object; no direct deterministic Fourier-band identification was promoted.

### G0 localized finite-space layer

Closed:

- hard-window Fourier basis correlation;
- centered `Fin (2N+1)` basis wrapper;
- actual zero-extended finite additive vectors;
- arbitrary complex coefficient transport;
- exact finite autocorrelation/correlation normalization.

### G1-A internal additive restriction

Closed:

```text
localizedWeilAdditiveRHS(localizedFiniteVector u)
  = quadraticForm(cutoffFreeMatrix) u.
```

This is an internal additive explicit-formula statement, not the external CCM `QW_lambda` theorem.

### G1-B0 direct source finite matrix

Closed:

```text
sourceEq44Matrix = cutoffFreeMatrix.
```

The later printed normalization is non-load-bearing for the direct finite matrix.

### Source-normalization repair

Closed:

```text
canonicalSourceMatrix = sourceEq44Matrix = cutoffFreeMatrix = dictionaryMatrix.
```

The canonical displacement theorem and rank-at-most-two theorem are exported on `canonicalSourceMatrix`.

## Current open gates on merged main

### G1-B1A — finite source kappa / source-sector map

**OPEN ON MERGED MAIN.**

Required source-valid content:

- `L = 2 log lambda > 0`;
- coordinate map `u -> log(lambda*u)`;
- explicit reverse map `x -> lambda^-1 exp(x)`;
- interval correspondence `[lambda^-1,lambda] <-> [0,L]`;
- source equation-(3.21) convention `V_n = kappa(U_n)`;
- arbitrary complex centered finite combinations;
- zero-extended source vectors on the actual multiplicative interval.

This gate must not silently treat a global real function as the source `E_N` vector.

### G1-B1B — source Hilbert/functional bridge

**OPEN.**

Formalize only the minimum external analytic interface required for Proposition 3.2:

- multiplicative Haar measure `d*u = du/u` as needed;
- the relevant L2/isometry interface from Proposition 3.2(i);
- log transport of convolution/involution;
- the `PsiSharp` / evenization normalization;
- Proposition 3.2(ii):
  `QW(kappa f,kappa g) = PsiSharp(F)`,
  with the exact source definition of `F`.

### G1-final — actual finite source restriction

**OPEN.**

Compose G1-A + source normalization + G1-B1A/B1B to prove the independent source-functional theorem

```text
QW_lambda restricted to E_N
  = canonicalSourceMatrix.
```

Do not define `QW_lambda` to return the desired matrix.

## Downstream route after G1

### T22-canonical — high-frequency/adversarial falsifier

Before investing heavily in finite-to-infinite closure, stress the **canonical** source matrix and exact source restriction.

No legacy-`finiteMatrix` inertia/PSD evidence may be used as canonical spectral-sign evidence.

### G23 — source form-core / minimum-eigenvalue transfer

The older roadmap split this into G2 form-core density and G3 Rayleigh-bottom convergence.

The present research hypothesis is that the exact source proposition packaging both facts should be ported directly if its hypotheses match the now-formalized objects. This is a **LEAD**, not yet a project theorem.

Target mathematical content:

```text
E = span{V_n : n in Z} is a core for QW_lambda
and
minEig(QW_lambda|E_N) -> inf QW_lambda.
```

### S0 — fixed-aperture source lock

The next source theorem must be pinned exactly before formalization:

```text
not RH
  -> exists fixed lambda > 1
     with inf QW_lambda < 0
```

or the exact source-equivalent statement actually available.

No source result may be upgraded beyond its literal hypotheses.

### Canonical finite obstruction

Only after G1 + G23 + S0 may the project claim a route of the form

```text
not RH
  -> eventual negative minimum eigenvalue
     of canonicalSourceMatrix(lambda,N).
```

That would still not prove RH. A separate finite-negative exclusion theorem would remain necessary.

## Dormant / composition tools

Potentially useful after canonical finite negativity becomes exact:

- R004 displacement/rank-two structure;
- parity/extremal-spectrum tools;
- prime-event / cutoff-flow structure;
- resolvent/Weyl eigenvalue motion;
- two-translate / Gram witness theorems;
- quantitative detector-aperture tools.

Each must be re-audited against the canonical normalization before use in a spectral-sign argument.

## Dead or quarantined identifications

Do not silently revive:

- `finiteMatrix = QW_lambda|E_N`;
- generic R002 smooth-taper `G-tilde(T)` = canonical CCM;
- Bombieri zero-index truncation = deterministic CCM Fourier truncation;
- fitted-small-commutator -> eigenvector convergence without an explicit generator and gap theorem.

See `../../DEAD_ROUTES.md`.

## Claim firewall

**PROVED on merged main:** finite/dictionary/zero-side/cutoff-free matrix identities, G0 localized finite-space geometry, G1-A additive restriction, direct Section-4 matrix normalization, canonical source normalization, canonical finite displacement.

**OPEN:** source `kappa` finite-sector theorem on merged main, multiplicative-Haar L2 interface, `PsiSharp`, ambient `QW_lambda`, actual restriction theorem, form-core/minimum-eigenvalue transfer, fixed-aperture negative-bottom implication, finite-negative exclusion, RH.

## Next-move rule

The semantic work-package names are authoritative. Historical PR numbers are execution history only and must not be used as stable roadmap identifiers.

Whenever one gate goes green, perform the post-green research pass before selecting the next gate.
