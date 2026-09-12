# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

## Current authority snapshot

```text
live main after merged PR #155 = 7bd3f1028d42272fcadc347c43371b992d9c0bd7
live main tree = 9a4f21ed55aa0cbdf54527164c2f5f96912c65de

latest theorem-bearing PR = #155
validated theorem head = ecfd075c07923e6fc80ab1a5b4f2d49c724f5577
validated theorem tree = 9a4f21ed55aa0cbdf54527164c2f5f96912c65de
RHRC #1005 / run 34720946254 = SUCCESS
Permansson #778 / run 34720946242 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

Live GitHub head + exact Lean/compiler/CI remain authoritative. The validated #155 head and merged `main` are different commits but share the same theorem tree.

## Current theorem ladder

```text
off-line zeta zero
  -> legal finite canonical negative obstruction                     PROVED
  -> global first bad + predecessor parity nonnegativity             PROVED
  -> shell/KKT/Schur/secular machinery                               PROVED
  -> source-explicit transfer                                       PROVED / #129
  -> exact canonical source-moment decomposition                    PROVED / #131
  -> denominator-free zero-shift kernel/source transport            PROVED / #134
  -> scalar-sensitive absolute canonical source energy              PROVED / #136
  -> exact source pairing + one-step determinant                    PROVED / #137
  -> aperture freedom / regular selected first bad                  PROVED / #140-#150
  -> interval-certified selected-residual falsification harness     TOOLING / #152
  -> retained whole-cell first-bad certificate                      PROVED / #153
  -> exact finite pole-prime discrepancy identity                   PROVED / #153
  -> finite discrepancy interval integrability                      PROVED / #155
  -> anchored Riesz primitives + AC / a.e. derivative API          PROVED / #155
  -> generic repeated-IBP / arbitrary-order conditional Riesz       PROVED / #155
  -> source-coordinate oddness + all even endpoint jets             PROVED / #155
  -> even parity M3 = 0                                             PROVED / #155

  -> complex production D-transport                                OPEN / NEXT
  -> production odd jets + exact Riesz orders 6/8                   OPEN
  -> retained transformed-negative certificate                      OPEN
  -> independent arithmetic sign for complete transformed residual  OPEN
  -> negative-root exclusion                                        OPEN
  -> outside-strip/trivial-zero seam + Mathlib RH wrapper            OPEN
  -> RH                                                               OPEN
```

## What #155 actually proved

PR #155 closes the **analytic legality** of smoothing, not the production order-6/order-8 instantiation and not the arithmetic sign problem.

### FB-03A — discrepancy integrability

**PROVED:** the finite prime cumulative staircase, smooth pole cumulative weight, and exact pole-prime discrepancy are interval-integrable on the physical aperture.

### FB-03B/C — anchored primitives and legal repeated integration by parts

**PROVED:** `canonicalPolePrimeRieszPrimitive` supplies left-anchored iterated primitives; positive-order primitives are absolutely continuous; their derivatives recover the previous primitive almost everywhere; the source-energy composed jets are smooth; and the generic Riesz identity is legal without differentiating the prime staircase.

The headline theorem remains conditional on explicit endpoint-jet hypotheses

```text
forall j, 1 <= j -> j <= r ->
  iteratedDeriv j (sourceAtomRealEnergy K x) 0 = 0.
```

### FB-03D — source-energy parity/even jets

**PROVED:** production `sourceAtomRealEnergy` is odd in the source coordinate, hence every even endpoint derivative at zero vanishes. Even reversal parity also forces centered moment `M3 = 0`.

**Not proved by #155:** the odd endpoint derivatives needed to instantiate production Riesz order 6 or 8.

## Current derived bridge — next theorem target

The post-green audit derives, but Lean has not yet theoremized,

```text
M0(u)=0
  -> g_u''(omega) = -(2*pi)^2 g_{D u}(omega)
```

for the genuine complex production source energy. Combined with the existing moment shift `M_k(Du)=M_{k+1}(u)`, the intended moment-prefix recursion is

```text
M0=...=M(r-1)=0
  -> g_u^(2r)(omega) = (-1)^r (2*pi)^(2r) g_(D^r u)(omega)
  -> g_u^(2r+1)(0) = 2*(-1)^r*(2*pi)^(2r)*|M_r(u)|^2.
```

This is **DERIVED / OPEN IN LEAN**. The implementation must prove the complex sesquilinear transport directly; a real-contraction theorem is not sufficient.

Expected consequences, still open in Lean:

```text
boundary-flat M0=M1=M2=0
  -> jets 1..6 vanish
  -> g^(7)(0) = -2*(2*pi)^6*|M3|^2

even boundary-flat + #155 M3=0
  -> jets 1..8 vanish
  -> g^(9)(0) = 2*(2*pi)^8*|M4|^2.
```

## Falsified shortcut

Exact `K=2` boundary-flat fixtures

```text
even: (1,-4,6,-4,1)
odd:  (1,-2,0,2,-1)
```

show that the relevant seventh/ninth source derivatives change sign. Therefore the route

```text
positive Riesz primitive + endpoint flatness
  -> pointwise fixed-sign smoothed integrand
```

is **DEAD**. Smoothing preserves/reexpresses the exact energy; it does not manufacture pointwise positivity.

The surviving sign target is the **complete integrated discrepancy minus archimedean/scalar residual**, using the retained whole-cell first-bad ancestry.

## Active path

```text
PROVED THROUGH #155
  off-line zero
    -> retained regular cell-minimal first-bad certificate
    -> exact canonical source-channel energy < 0
    -> exact finite pole-prime discrepancy normal form
    -> legal arbitrary-order conditional Riesz representation
    -> all even source-energy endpoint jets + even M3=0

NOW — FB-03E
  prove complex production source-coordinate D-transport
    -> moment-prefix recursion
    -> production odd endpoint jets
    -> exact unconditional Riesz order 6 / even order 8

THEN — FB-03F
  compose that transformed representation with the retained #153
  first-bad negative certificate / ExceptionalZero state

THEN — FB-04
  formulate specific arithmetic sign mechanisms for the COMPLETE transformed residual
  and use the #152 harness to falsify them before theorem investment

TARGET
  independent nonnegative sign on the exact same forced state
    -> contradiction with retained transformed negative residual
    -> negative-root exclusion
    -> explicit outside-strip/trivial-zero seam
    -> Mathlib RiemannHypothesis wrapper
```

## Documentation authority

Current living state is maintained in:

- `research/RHRC/CURRENT_RESEARCH_PLAN.md`;
- `research/RHRC/RESEARCH_LEADS.md`;
- `research/RHRC/RESEARCH_LEADS_POST_155_RIESZ_D_TRANSPORT_FRONTIER_DELTA.md`;
- `research/RHRC/OBSTRUCTION_LEDGER.md` / `DEAD_ROUTES.md`;
- `research/RHRC/DOCUMENTATION_AUTHORITY.md`;
- `research/RHRC/VALIDATION_PROTOCOL.md`;
- `research/RHRC/routes/R003_ccm_bridge/README.md`;
- `research/RHRC/control_v2/README.md`.

Older dated deltas, external reviews, countermodel reports and release audits remain historical evidence and are not rewritten to look current.

## Permanent firewalls

- RH remains OPEN.
- compiler/CI validity attaches to the exact checked object.
- theorem authority through #155 is not automatic machine claim promotion.
- a retained negative certificate is not a contradiction.
- exact discrepancy identity is not a sign theorem.
- generic Riesz smoothing is not production Riesz 6/8 until the odd jets are theoremized.
- a real contraction identity is not automatically the complex production source-energy identity.
- pointwise positivity of the smoothed integrand is falsified as a universal mechanism.
- interval-certified finite numerics are not Lean theorem authority.
- generic/modified-source countermodels are not zeta counterexamples.
- `D` remains algebraic, not unitary/isometric.
- negative-root exclusion is not the terminal Mathlib `RiemannHypothesis` statement without the final seam.

**RH remains OPEN.**
