# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

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

Live GitHub head + exact Lean compiler + CI are authority. Control v2 may select research actions but may not promote theorem or terminal RH status.

## Theorem-backed route

```text
finite off-line-zero obstruction / legal approximation                 PROVED
canonical finite negative obstruction                                  PROVED / #94
centered N-flow / parity / first-bad / shell / Schur package            PROVED / #100-#128
source-explicit cross-parity transfer                                   PROVED / #129
exact canonical source-moment decomposition                             PROVED / #131
denominator-free zero-shift source transport                            PROVED / #134
absolute canonical source-energy decomposition                          PROVED / #136
exact canonical source pairing + one-step determinant                   PROVED / #137
regular selected first-bad endpoint                                     PROVED / #140-#150
selected-residual falsification/certification harness                   TOOLING / #152
retained full first-bad / negative-energy certificates                  PROVED / #153
exact finite pole-prime discrepancy / full-channel normal form          PROVED / #153
finite discrepancy integrability                                        PROVED / #155
anchored Riesz primitives + AC / a.e. derivative                        PROVED / #155
generic legal repeated-IBP / conditional Riesz representation           PROVED / #155
source oddness + all even endpoint jets                                 PROVED / #155
even-parity centered moment M3 = 0                                     PROVED / #155

complex production source-coordinate D transport                        OPEN / NOW
production odd jets + exact Riesz orders 6/8                            OPEN
retained transformed-negative first-bad wrapper                         OPEN
complete transformed-residual arithmetic sign                           OPEN
negative-root exclusion                                                  OPEN
outside-strip/trivial-zero seam + terminal RH bridge                     OPEN
RH                                                                       OPEN
```

## Post-#155 state

The analytic-legality problem is now largely closed. The prime staircase is never differentiated: #155 integrates the exact finite discrepancy into left-anchored primitives, proves positive-order absolute continuity and the a.e. derivative relation, and supplies a generic repeated-integration-by-parts/Riesz theorem with explicit endpoint-jet hypotheses.

The source-energy side also advanced: production `sourceAtomRealEnergy` is odd in the source coordinate, every even endpoint derivative at zero vanishes, and even reversal parity kills `M3`.

What #155 does **not** prove is the missing odd endpoint cancellation needed for unconditional production order 6/8.

## Immediate theorem frontier — FB-03E

The audited post-green calculation derives

```text
M0(u)=0
  -> g_u''(omega)=-(2*pi)^2 g_(D u)(omega)
```

for the genuine complex production energy. Together with the existing theorem `M_k(Du)=M_(k+1)(u)`, the intended recursion is

```text
M0=...=M(r-1)=0
  -> g_u^(2r)(omega)=(-1)^r*(2*pi)^(2r)*g_(D^r u)(omega)
  -> g_u^(2r+1)(0)=2*(-1)^r*(2*pi)^(2r)*|M_r(u)|^2.
```

**Status: DERIVED / OPEN IN LEAN.**

Implementation must stay on the complex production object:

```text
sourceEntrySecondDerivative
  -> entrywise rank-two identity
  -> complex source matrix
  -> sum against conj(u_i)*u_j
  -> annihilate rank-two correction from sum u_i=0
  -> identify D A D with source energy of indexMatrix *ᵥ u.
```

Do not prove only a real contraction theorem and silently transport it.

## Exact falsification memory

The legal boundary-flat `K=2` vectors

```text
even: (1,-4,6,-4,1)
odd:  (1,-2,0,2,-1)
```

show that the relevant seventh/ninth source derivatives change sign. Therefore

```text
positive Riesz primitive + endpoint flatness
  -> pointwise fixed-sign smoothed integrand
```

is **DEAD** as a universal mechanism.

Smoothing remains valuable as an exact representation. The surviving sign problem concerns the **complete integrated discrepancy minus reduced archimedean/scalar residual**, possibly using stationarity, whole-cell minimality, predecessor transfer, or a different arithmetic invariant.

## Current execution priority

1. **FB-03E — complex D-transport / odd jets.** Prove the genuine production identity and moment-prefix recursion; instantiate the generic #155 theorem to exact order 6, and to order 8 under even parity.
2. **FB-03F — retained transformed-negative wrapper.** Compose the resulting production Riesz identity with the retained #153 first-bad certificate / ExceptionalZero state without adding hypotheses.
3. **FB-04 — mechanism falsification.** Formulate a specific arithmetic inequality for the complete transformed residual, then use the #152 harness to try to kill it. Do not merely rescan for negative total energy.
4. **FB-05 — prove the scoped sign** on the exact retained forced state.
5. **FB-06 — compose same-state signs to exclude the hypothetical off-line zero.**
6. **FB-07 — close outside-strip/trivial-zero seam and terminal Mathlib wrapper.**

Universal A4b2b domination remains a broad fallback if a genuinely independent canonical arithmetic mechanism appears.

## Formal endpoint and derived interpretation

At the selected retained state:

```text
whole-cell K* minimality      theorem-backed
smaller sizes good at L       theorem-backed
A>=0                          theorem-backed
A regular                     theorem-backed
A>0                           DERIVED finite Hermitian consequence
unique x0 with A x0=b         theorem-backed
lam<0 + explicit root         theorem-backed
Ecanonical(c-x0)<0            theorem-backed
```

The exact pole-minus-prime channel is theorem-backed as one finite cumulative discrepancy pairing. #155 supplies a legal conditional Riesz transform of that pairing but no arithmetic sign.

## Current research records

- `CURRENT_RESEARCH_PLAN.md` — execution order and theorem gates.
- `RESEARCH_LEADS_POST_155_RIESZ_D_TRANSPORT_FRONTIER_DELTA.md` — newest audited post-green synthesis.
- `external_reviews/ASTRA_POST_155_RH_PATH_ASSESSMENT_2026_09_13.md` — external review provenance; discovery evidence only.
- `countermodels/POST_155_RIESZ_POINTWISE_SIGN_COUNTERMODELS_2026_09_13.md` — exact finite falsification memory for the dead pointwise-sign shortcut.
- `OBSTRUCTION_LEDGER.md` — accumulated reusable blockers.
- `DEAD_ROUTES.md` — quarantined/dead routes.
- `routes/R003_ccm_bridge/README.md` — active route theorem surface.
- `control_v2/README.md` — executable research routing.

Older dated deltas and route settlements remain historical evidence and are not rewritten to look current.

## Permanent firewalls

- RH remains OPEN.
- theorem authority is through #155; machine claim promotion remains separate.
- negative exact selected energy is not a contradiction without an independent nonnegative sign theorem.
- exact discrepancy identity and legal smoothing are not arithmetic sign theorems.
- generic conditional Riesz smoothing is not unconditional production order 6/8.
- real-contraction derivative transport does not establish the complex production theorem.
- pointwise fixed-sign smoothed-integrand positivity is falsified as a universal route.
- external derivations and numerical experiments are not Lean authority.
- interval-certified finite numerical failures are scoped falsification evidence only.
- `D` remains algebraic, not unitary/isometric.
- terminal negative-root exclusion still needs the outside-strip/trivial-zero seam before the Mathlib `RiemannHypothesis` wrapper.

**RH remains OPEN.**
