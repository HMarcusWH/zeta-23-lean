# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

## Current authority snapshot

```text
live main after merged PR #140 = fa96196b5bd6ed754853b0bdacee1dbd2356022f
live main tree = 2015404927540ae79a64469af82813463694b71d

theorem-state anchor = PR #140 merge fa96196b5bd6ed754853b0bdacee1dbd2356022f
validated theorem head = 77b52cfc73dfd83d2a0ed4373befba97d77e48e5
validated theorem tree = 2015404927540ae79a64469af82813463694b71d
RHRC #882 = SUCCESS
Permansson #655 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

Live GitHub head + exact Lean compiler + CI are authority. Control v2 may select research actions but may not promote theorem or terminal RH status.

## Theorem-backed route

```text
finite off-line-zero obstruction / legal approximation                 PROVED
canonical finite negative obstruction                                  PROVED / #94
constrained algebra / Euclidean sector                                  PROVED / #96-#98
exact centered N-flow + parity / first-bad / one-dimensional shell      PROVED / #100-#112
exact shifted/zero-shift Schur and secular package                      PROVED / #113-#128
source-explicit cross-parity transfer                                   PROVED / #129
exact canonical source-moment decomposition                             PROVED / #131
denominator-free zero-shift source transport                            PROVED / #134
absolute canonical source-energy decomposition                          PROVED / #136
exact canonical source pairing + one-step determinant                   PROVED / #137
off-line zero -> q_c<0 OR exists w, Delta(w)<0                         PROVED / #137
aperture freedom at every sufficiently large L                          PROVED / #140
fresh global-first-bad selection at every sufficiently large L          PROVED / #140
actual predecessor det!=0 <-> injective + unique preimage               PROVED / #140
frozen prime-cell equality + threshold atom zero + scalar -log(L) split PROVED / #140

fixed-cell finite regular-aperture selection                             OPEN / NOW
regular minimizing-trial Schur-energy sign                              OPEN / NEXT
universal canonical one-step domination                                 OPEN / BROAD FALLBACK
negative-root exclusion                                                  OPEN
explicit terminal RH bridge                                              OPEN
RH                                                                       OPEN
```

## Post-#140 research reroute

The post-#138 Astra audit remains an important circularity/falsification record, but #140 changes the executable A4R quantifiers.

A hypothetical off-line zero now forces finite canonical negativity at **every sufficiently large aperture**. Therefore we can choose a convenient frozen cutoff cell first, obtain a finite witness inside it, then regularize only the finitely many predecessor sizes relevant to that witness.

The primary route is now:

```text
one large cutoff cell (log Q, log(Q+1))
  -> choose interior L1
  -> #140 gives finite negative witness (N,u)
  -> preserve its strict negativity on a small interval
  -> avoid singular determinants for both parities and k<=N
  -> choose nearby L2 in the same cell
  -> fresh global-first-bad reselection at L2.
```

This avoids countable all-size Baire machinery and avoids threshold crossing in the load-bearing regularization step.

## Current execution priority

1. **A4R1 — fixed-cell continuity and actual predecessor analyticity.** Work on the exact frozen production source and `intrinsicPredecessorBlock`.
2. **Determinant nonidentity and dense fixed-block regularity.** The #140 `-log(L)` scalar split is already proved; the unresolved issue is the full analytic remainder, especially the archimedean channel.
3. **Finite simultaneous regularization.** For an arbitrary finite horizon `M`, intersect the finitely many dense regular sets for both parities.
4. **Compose with #140 aperture freedom.** Obtain `(N,u)` first, take `M=N`, preserve negativity locally, regularize, then reselect first-bad.
5. **Package the regular first-bad countercertificate.** Use the #140 unique-preimage theorem instead of introducing a bespoke inverse.
6. **Analyze the full minimizing-trial Schur remainder.** Preserve exact prime/arch/scalar cancellation.
7. **Prove the regular source-energy sign.** Seek an independent canonical arithmetic theorem proving `Ecanonical(c-x0)>=0` for the unique `A x0=b` trial.
8. **Compose to contradiction and then the terminal Mathlib RH wrapper.**

Universal A4b2b domination remains a broad fallback if a genuinely independent positive source representation or exact remainder appears.

## Analytic lead and resurrected infrastructure

The candidate nonidentity mechanism is a genuine log-cover continuation, schematically

```text
Ahat(z) = -z I + Rhat(z)
Rhat(z+2*pi*i)=Rhat(z).
```

If `det Ahat` vanished identically, periodicity would force a fixed `d x d` matrix to admit `d+1` distinct shifted eigenvalues. This is a LEAD until the full production continuation is theoremized.

The old dictionary/gamma infrastructure is newly relevant:

```text
Zeta23/CCM/DictionaryArchPhysical.lean
Zeta23/CCM/DictionaryArchBridge.lean
```

These theorem-lock physical arch normalization and a summable digamma representation and should be inspected before proving new raw parameter-dependent integral holomorphy.

## Post-#138 constraints still active

Preserve these at their correct evidence levels:

- **DERIVED:** under predecessor PSD and one-dimensional shell, universal `q_c>=0` plus `Delta(w)>=0` is equivalent to successor positivity.
- **DERIVED:** `Delta(P_kerA b)=-||P_kerA b||^4`.
- **DERIVED / external exact-check:** `d=-(6/(2*N-1))a` for the correction vectors.
- **DERIVED / external symbolic:** atomwise determinant positivity fails at the leading tested source-atom coefficient.
- **EXPERIMENTAL SIGNAL:** sampled canonical Schur endpoints can be residues of extremely large cancellation.
- **EXPERIMENTAL SIGNAL:** tiny modified prime-weight changes can flip successor sign while predecessors remain positive.

These findings constrain proof design; they do not establish RH.

## Permanent firewalls

- RH remains OPEN.
- theorem authority is through #140 only.
- aperture freedom is PROVED; dense regularity is OPEN.
- regularity is not positivity.
- regular Schur-energy nonnegativity is OPEN.
- universal domination is not a research reduction if its proof merely restates successor PSD.
- external exact checks and numerical experiments are not theorem authority.
- no all-size Baire construction is required unless the finite-cell route fails for a theoremized reason.
- no inverse is load-bearing before regularity; prefer the unique-preimage theorem.
- no factorwise division by `alpha`, `Gamma`, overlap or source moment without theoremized nonzeroness.
- D is algebraic, not unitary/isometric.
- machine claim promotion remains separate.

## Current research records

- `CURRENT_RESEARCH_PLAN.md` — execution order and gates.
- `RESEARCH_LEADS_POST_140_APERTURE_FREEDOM_DELTA.md` — newest research delta.
- `RESEARCH_LEADS_POST_138_ASTRA_DELTA.md` — historical pre-#140 reroute.
- `external_reviews/ASTRA_POST_138_RH_PATH_ASSESSMENT_2026_09_09.md` — external-review provenance.
- `countermodels/POST_138_ASTRA_DIAGNOSTICS_2026_09_09.md` — discovery/falsification findings.
- `OBSTRUCTION_LEDGER.md` — reusable blockers.
- `DEAD_ROUTES.md` — quarantined routes.
- `routes/R003_ccm_bridge/README.md` — active route theorem surface.
- `control_v2/README.md` — executable research routing.

**RH remains OPEN.**