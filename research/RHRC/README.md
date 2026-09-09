# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

## Current authority snapshot

```text
live main after merged PR #138 = ebf289bdfdde69020bee0d1571047f155e5de4db
live main tree = d26cd83709437260d0a16630d90c73a93f64c975

theorem-state anchor = PR #137 merge fa2f209a6eb8b4059968e8d61239d80588ca256c
validated theorem head = 64988e142590c82bd0ad43604279ede9a8e85eff
validated theorem tree = e3de4dc0377f0124832822b6f97ab5bbd7718640
RHRC #878 = SUCCESS
Permansson #651 = SUCCESS

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
exact canonical source pairing                                          PROVED / #137
one-step determinant + domination sufficiency                           PROVED / #137
off-line zero -> q_c<0 OR exists w, Delta(w)<0                         PROVED / #137

regular-aperture simultaneous predecessor selection                     OPEN / NOW
regular minimizing-trial Schur-energy sign                              OPEN / NEXT
universal canonical one-step domination                                 OPEN / BROAD FALLBACK
negative-root exclusion                                                  OPEN
explicit terminal RH bridge                                              OPEN
RH                                                                       OPEN
```

## Post-#138 research reroute

The post-#138 Astra audit sharpened the existing circularity warning:

```text
A>=0 and dim(shell)=1:
q_c>=0 AND forall w, Delta(w)>=0
  <-> successor one-step form >=0.
```

Therefore the universal determinant certificate remains an exact sufficient theorem but is no longer the immediate research frontier.

The active strategy is to remove singular/resonant predecessor geometry first, without proving successor positivity.

## Current execution priority

1. **A4R — regular-aperture/log-lift selection.** Prove dense simultaneous predecessor injectivity/positive definiteness for the finite family relevant to a preserved strict negative witness, then reselect global first-bad at the moved aperture.
2. **Package one regular countercertificate.** Both predecessors positive definite, unique `x0=A^-1b`, and the existing source-energy/Schur machinery attached to the same witness.
3. **Analyze the full minimizing-trial Schur remainder.** Work on `u0=c-A^-1b`, channel-by-channel but preserving exact mixed cancellation.
4. **Prove the regular source-energy sign.** Seek an independent canonical arithmetic estimate proving `Ecanonical(u0)>=0`, equivalently `<b,A^-1b><=q_c`.
5. **Compose to contradiction and then the terminal Mathlib RH wrapper.**

Universal A4b2b domination is retained as a broad fallback if a genuinely independent positive source representation or exact remainder appears.

## Why A4R now has information value

Regularity is not positivity. Generic regular negative examples exist, so selecting a nearby aperture with positive-definite predecessor blocks does not assume the desired conclusion.

The candidate proof uses the exact scalar normalization:

```text
M_Q(L)=-log(L)I+B_Q(L)
L=exp(z)
```

and a periodic log-lift determinant nonidentity argument. It must still discharge exact frozen-cutoff analyticity, threshold continuity, basis/Gram, simultaneous finite avoidance, negative-witness continuity, fresh first-bad reselection, and predecessor-compression obligations.

## Post-#138 derived and experimental constraints

Preserve these at their correct evidence levels:

- **DERIVED:** `Delta(P_kerA b)=-||P_kerA b||^4`.
- **DERIVED:** the safe negative root selects an explicit predecessor direction with a closed negative determinant formula.
- **DERIVED / external exact-check:** `d=-(6/(2*N-1))a` for the two correction vectors.
- **DERIVED / external symbolic:** atomwise determinant positivity fails at the leading nonzero two-vector coefficient in the tested BF sectors.
- **EXPERIMENTAL SIGNAL:** sampled canonical Schur endpoints can be residues of extremely large cancellation.
- **EXPERIMENTAL SIGNAL:** tiny modified prime-weight changes can flip successor sign while predecessors remain positive.

These findings constrain proof design; they do not establish an RH theorem.

## Permanent firewalls

- RH remains OPEN.
- theorem authority remains #137 until new Lean/CI evidence exists.
- regular-aperture selection is OPEN.
- regular Schur-energy nonnegativity is OPEN.
- universal domination is not a research reduction if its proof merely restates successor PSD.
- external exact checks and numerical experiments are not theorem authority.
- no `A^-1` at zero before regularity.
- no factorwise division by `alpha`, `Gamma`, overlap or source moment without theoremized nonzeroness.
- D is algebraic, not unitary/isometric.
- machine claim promotion remains separate.

## Current research records

- `CURRENT_RESEARCH_PLAN.md` — execution order and gates.
- `RESEARCH_LEADS_POST_138_ASTRA_DELTA.md` — newest research delta.
- `external_reviews/ASTRA_POST_138_RH_PATH_ASSESSMENT_2026_09_09.md` — external-review provenance.
- `countermodels/POST_138_ASTRA_DIAGNOSTICS_2026_09_09.md` — discovery/falsification findings.
- `RESEARCH_LEADS_POST_137_DELTA.md` — historical post-#137 pre-Astra frontier.
- `OBSTRUCTION_LEDGER.md` — reusable blockers.
- `DEAD_ROUTES.md` — quarantined routes.
- `routes/R003_ccm_bridge/README.md` — active route theorem surface.
- `control_v2/README.md` — executable research routing.

**RH remains OPEN.**