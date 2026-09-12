# RHRC living research leads ledger

> **Claim firewall: RH remains OPEN.**
>
> This is the current research inventory/index, not a theorem registry. Formal authority remains the exact Lean/compiler/CI state plus the deliberately separate machine claim surfaces.

## Current theorem / research authority

```text
live main after merged PR #155 = 7bd3f1028d42272fcadc347c43371b992d9c0bd7
live main tree = 9a4f21ed55aa0cbdf54527164c2f5f96912c65de

latest theorem-bearing PR = #155
validated theorem head = ecfd075c07923e6fc80ab1a5b4f2d49c724f5577
validated theorem tree = 9a4f21ed55aa0cbdf54527164c2f5f96912c65de
RHRC #1005 / run 34720946254 = SUCCESS
Permansson #778 / run 34720946242 = SUCCESS

newest post-green delta = RESEARCH_LEADS_POST_155_RIESZ_D_TRANSPORT_FRONTIER_DELTA.md
current execution SSOT = CURRENT_RESEARCH_PLAN.md
RH = OPEN
```

Live GitHub head and exact compiler/CI evidence remain authoritative.

## Historical full-ledger preservation

The former large per-entry inventory is preserved unchanged as

```text
RESEARCH_LEADS_LEGACY_FULL_THROUGH_110.md
```

Use it for archaeology, old lead IDs, provenance and historical route context. Older dated `RESEARCH_LEADS_POST_*.md` files remain chronological historical records.

## Status vocabulary

Formal status:

- **PROVED** — exact statement established by Lean/compiler/CI.
- **DERIVED** — direct mathematical consequence not separately theoremized.
- **LEAD / HYPOTHESIS** — mathematically motivated route, not established.
- **EXPERIMENTAL SIGNAL** — numerical/search/discovery evidence only.
- **OPEN** — exact intended statement not established.

Research status never upgrades formal status.

## Current promoted frontier inputs

### Retained regular first-bad certificate

**Research status:** PROMOTED  
**Formal status:** PROVED / #153

```text
RegularCellMinimalFirstBadCertificate
RegularCellMinimalNegativeEnergyCertificate
exists_regularFirstBad_negativeEnergyCertificate_of_offLine_zero
```

The whole-cell first-bad ancestry, selected regular predecessor, predecessor nonnegativity, negative explicit root, exact `A x0=b`, and negative exact canonical energy are retained in theorem-facing structures.

### Exact pole-prime discrepancy

**Research status:** PROMOTED  
**Formal status:** PROVED / #153

```text
canonicalPolePrimeDiscrepancy
canonicalPolePrimeDiscrepancyEnergy
matrixRealEnergy_pole_sub_prime_eq_discrepancy
canonicalSourceChannelEnergy_eq_discrepancy
```

Pole and prime cancellation is now an exact finite Lean theorem under the production normalization.

### Generic legal Riesz smoothing

**Research status:** PROMOTED  
**Formal status:** PROVED / #155

#155 proves finite discrepancy integrability, left-anchored iterated primitives, positive-order absolute continuity, a.e. derivative recovery, smooth composed source jets, and the generic arbitrary-order Riesz identity under explicit endpoint-jet hypotheses.

It does **not** prove unconditional production order 6/8.

### Production source parity/even jets

**Research status:** PROMOTED  
**Formal status:** PROVED / #155

Production source energy is odd in the source coordinate, all even endpoint derivatives vanish, and even reversal parity kills `M3`.

### Selected-residual certification harness

**Research status:** TESTING INFRASTRUCTURE  
**Formal status:** TOOLING / #152; no theorem authority

The exact-rational geometry + production numerical scout + Arb replay lane can falsify finite scoped sign mechanisms. It does not prove a sign by repeated success and does not automatically certify whole-cell ancestry.

## Active lead — FB-03E complex source-coordinate D transport

**Research status:** ACTIVE / HIGHEST LEVERAGE  
**Formal status:** DERIVED / OPEN IN LEAN

Target:

```text
M0(u)=0
  -> g_u''(omega)=-(2*pi)^2 g_(D u)(omega)
```

for the genuine complex production energy `g_u = sourceAtomRealEnergy K u`.

The entrywise calculation gives a rank-at-most-two defect. Its complex Hermitian quadratic form vanishes under `sum u=0`. The implementation must make that cancellation theorem-backed rather than importing a real-vector contraction theorem by analogy.

Preferred proof spine:

```text
sourceEntrySecondDerivative
  -> entrywise rank-two source-matrix identity
  -> complex contraction against conj(u_i)*u_j
  -> zero-sum annihilation
  -> identify D A D with source energy of indexMatrix *ᵥ u.
```

## Active lead — moment-prefix recursion / production odd jets

**Research status:** ACTIVE / SAME PR  
**Formal status:** DERIVED / OPEN IN LEAN

Use the already proved shift

```text
M_k(Du)=M_(k+1)(u)
```

to target

```text
M0=...=M(r-1)=0
  -> g_u^(2r)(omega)=(-1)^r*(2*pi)^(2r)*g_(D^r u)(omega)
  -> g_u^(2r+1)(0)=2*(-1)^r*(2*pi)^(2r)*|M_r(u)|^2.
```

Expected production consequences:

```text
boundary-flat -> jets 1..6 vanish
boundary-flat -> g^(7)(0)=-2*(2*pi)^6*|M3|^2

even boundary-flat + #155 M3=0 -> jets 1..8 vanish
even -> g^(9)(0)=2*(2*pi)^8*|M4|^2.
```

These remain DERIVED until compiler-validated.

## Active lead — exact production Riesz 6/8

**Research status:** ACTIVE / SAME PR  
**Formal status:** OPEN

Instantiate the already-proved generic #155 Riesz theorem:

```text
boundary-flat -> exact order-6 Riesz identity
even boundary-flat -> exact order-8 Riesz identity.
```

No arithmetic sign theorem belongs in this step.

## Immediate downstream — retained transformed-negative certificate

**Research status:** READY AFTER FB-03E  
**Formal status:** OPEN

Compose the production Riesz specializations with the retained #153 first-bad certificate and ExceptionalZero wrapper. The goal is

```text
off-line zero
  -> retained regular first-bad state
  -> exact order-6/order-8 transformed residual < 0
```

without adding hypotheses not already present on the retained state.

Once green, FB-03 is genuinely closed.

## Dead route — pointwise positivity after smoothing

**Research status:** REFUTED  
**Formal status:** exact finite falsification of the proposed mechanism; not an RH result

The exact boundary-flat `K=2` vectors

```text
even: (1,-4,6,-4,1)
odd:  (1,-2,0,2,-1)
```

show the relevant seventh/ninth source derivatives change sign. Thus

```text
positive Riesz primitive + endpoint flatness
  -> pointwise fixed-sign smoothed integrand
```

is not a valid universal closing theorem.

The Riesz representation survives; the pointwise sign interpretation does not.

## Active lead — complete transformed-residual arithmetic sign

**Research status:** ACTIVE AFTER FB-03  
**Formal status:** OPEN

The surviving target is the **complete integrated discrepancy minus reduced archimedean/scalar residual**, under the exact retained whole-cell first-bad ancestry.

Candidate mechanism families worth deriving and immediately falsifying:

- stationarity `A x0=b` inside the transformed representation;
- transfer to smaller-size good predecessor energies;
- whole-cell minimality across the fixed cutoff cell;
- exact cancellation identities that keep discrepancy and archimedean pieces coupled;
- cross-parity compensation if a genuinely invariant combined quantity exists.

Do not invest in a theorem before specifying an independently meaningful inequality/mechanism.

## Lead — combined-parity invariant

**Research status:** TEST FIRST  
**Formal status:** LEAD / HYPOTHESIS

The first surviving local cutoff contributions have opposite parity signs. Candidate diagnostics include

```text
S_even + S_odd
S_even * S_odd
```

or another parity-combined invariant.

Cheapest test: compute the same-cell quantities across prime-power thresholds and inside cells. If sign/monotonicity fails, discard immediately. If a combined quantity survives while the individual sectors oscillate, that is new information worth theorem work.

## Broad fallback — universal one-step domination

**Research status:** DORMANT / ROUTABLE FALLBACK  
**Formal status:** OPEN

`canonicalOneStepDomination` is a theorem-backed sufficient certificate, but under predecessor nonnegativity and a one-dimensional shell it essentially repackages the missing successor positivity. It becomes research-useful only if an independent canonical arithmetic mechanism proves it.

## Quarantined current shortcuts

Current high-priority quarantines/dead routes include:

- generic first-bad Hermitian/parity/KKT structure without exact canonical arithmetic;
- factorwise `alpha` / `Gamma` / overlap / source-moment nonvanishing or division;
- shift-invariant data used to infer absolute spectral sign;
- atom-by-atom positive determinant/SOS;
- independent coarse pole/prime/arch/scalar majorants;
- global aperture Loewner monotonicity;
- global minimizing-trial Schur monotonicity;
- universal positive elementary source-atom energy;
- direct coth/deck common-lattice identification;
- real-vector D transport silently promoted to the complex production energy;
- pointwise fixed-sign smoothed-integrand positivity.

## Update law

After every meaningful green result:

1. verify the exact checked head/tree and theorem surface;
2. update claim/route registries only when their own authority changes;
3. update the active route README and `CURRENT_RESEARCH_PLAN.md`;
4. add a dated post-green delta;
5. update this compact living index when lead status/execution priority changes;
6. preserve old dated deltas and the legacy full ledger as historical evidence;
7. resurrect a dead route only by naming the premise that changed.

## Standing research questions

1. What became possible that was not possible before?
2. Which assumptions disappeared or can now be weakened?
3. Which dead route had exactly that missing prerequisite?
4. Can multiple proved results compose into a qualitatively stronger restriction?
5. Can we attack the admissible counterexample space rather than RH directly?
6. What is the cheapest falsifier for the most promising new clue?
7. Does the result compress the dependency graph?
8. Is a proposed next lemma secretly RH-equivalent?
9. Are we using the canonical sign-authoritative object?
10. Does any conclusion rely on an unproved identification between distinct finite/operator objects?

**Current highest-information question:** can the derived complex source-coordinate D-transport be theoremized exactly on the production energy, thereby closing the odd jets and exact Riesz 6/8 specializations?

**RH remains OPEN.**
