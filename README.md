# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

## Current authority snapshot

~~~text
theorem-state anchor = PR #110 merge 07e0c845d128831b244b13503c9640b934bf4416
validated theorem head = ca0c389827520e2005390637742389819dc97068
validated theorem tree = f2e9985ac976c83ecfa7f5dbce64b1e0193680b0
live main at sync start = 07e0c845d128831b244b13503c9640b934bf4416
theorem-bearing merged through = PR #110
RHRC #738 = SUCCESS
Permansson #511 = SUCCESS
CCM build = SUCCESS
ExceptionalZero build = SUCCESS
normalization/source firewall = SUCCESS
forbidden-placeholder gate = SUCCESS
#109 printed axiom surface = [propext, Classical.choice, Quot.sound]
#110 promoted theorem-specific axiom surface = revalidated by this control-plane PR
RH = OPEN
~~~

PR #110 is merged. Its final theorem head and merged `main` have the identical theorem tree `f2e9985ac976c83ecfa7f5dbce64b1e0193680b0`.

## Current RH-directed theorem ladder

~~~text
off-line zeta zero
  -> compact C² pole-neutral negative W test                       PROVED
  -> strict aperture + legal finite approximation                 PROVED
  -> canonical finite negative obstruction                        PROVED / #94
  -> constrained algebra / Hermitianity / displacement            PROVED / #96
  -> Euclidean constrained sector / exact dimensions              PROVED / #98
  -> exact centered N-flow / fixed-L negative tail                PROVED / #100
  -> exact reversal symmetry / even commutator collapse           PROVED / #102
  -> direct parity geometry / D : V+ ≃ V-                         PROVED / #103
  -> fixed parity bad tail + least bad size                       PROVED / #105
  -> predecessor parity sector nonnegative                        PROVED / #105
  -> exact Euclidean successor parity shell finrank 1             PROVED / #105
  -> parity-constrained Euclidean compression                     PROVED / #107
  -> exact compressed/self quadratic agreement                    PROVED / #107
  -> symmetric compressed canonical operator                      PROVED / #107
  -> ParityBad -> genuine negative Rayleigh eigenmode             PROVED / #107
  -> predecessor nonnegativity transported to successor matrix    PROVED / #107
  -> negative first-bad eigenmode is not inherited                PROVED / #107
  -> off-line zero -> first-bad negative spectral endpoint        PROVED / #107
  -> nonzero 1D successor-shell projection                        PROVED / #109
  -> exact even/odd parity normal spaces                          PROVED / #109
  -> exact parity KKT residual                                    PROVED / #109
  -> off-line zero -> shell + KKT first-bad endpoint              PROVED / #109
  -> Euclidean algebraic D-equivalence                            PROVED / #110
  -> M(Du)=D(Mu) on even constrained sector                       PROVED / #110
  -> g_N = P_- d³ != 0 for N>=2                                  PROVED / #110
  -> range(T_- D - D T_+) <= C g_N                               PROVED / #110
  -> parity compressed intertwining defect finrank <= 1           PROVED / #110
  -> conjugated same-space parity defect finrank <= 1             PROVED / #110

NOW — FIRST-BAD-RIGIDITY-D
  intrinsic predecessor/shell block geometry inside successor subtype
  first-bad eigenmode = predecessor + nonzero 1D shell component
  shifted A-lam I invertibility and scalar Schur/Feshbach equation
  explicit rank-one factorization if the defect functional can be isolated
  pullback cubic channel vs first-bad shell
  parity nullity-difference <= 1
  common-resonance vs one-channel-resolvent dichotomy

THEN
  classify/rule out simultaneous parity resonance
  compose the scalar shell and scalar parity-defect channels
  attack the first-bad state itself

PARALLEL
  source-faithful G1-B1B -> G1-final -> S-NEG -> G23

RH                                                                 OPEN
~~~

## What #109 and #110 changed

PR #109 upgraded #107 non-inheritance to a genuine nonzero projection onto the already-proved one-dimensional ambient successor parity shell. It also proves the exact parity normal spaces and converts any compressed parity eigenmode into the explicit KKT residual

~~~text
even: Mv = lam v + a0*1 + a2*d²
odd:  Mv = lam v + a1*d.
~~~

The RH-directed ExceptionalZero endpoint now includes the negative eigenpair, predecessor nonnegativity, nonzero shell projection, one-dimensional shell and exact KKT residual.

PR #110 composes that geometry with the exact even commutator collapse. Applying D to the even normal channel sends `span{1,d²}` to `span{d,d³}`; odd compression kills `d`, leaving the single projected cubic channel `g_N=P_-d³`. The compressed even/odd intertwining defect therefore has range in one explicit line and complex finrank at most one. Algebraic conjugation through D gives the same rank bound on one common even carrier.

## Immediate derived consequences

**DERIVED / not yet separately formalized:**
- codimension-one predecessor nonnegativity still implies negative index at most one; together with the proved negative eigenvalue this suggests negative index exactly one / a unique negative eigenline;
- rank-one perturbation gives a parity nullity-difference bound of at most one at each scalar after algebraic conjugation;
- away from common parity resonance, the eigenvector equation reduces to one opposite-parity resolvent channel.

These are not promoted theorem claims yet.

## Permanent firewalls

- The #109 shell theorem is ambient-Euclidean; a fully intrinsic successor-subtype block decomposition remains open.
- `v ∉ predecessorImage` does not mean `v` lies purely in the shell.
- the successor shell is not proved invariant.
- D-equivalence is algebraic, not unitary or isometric.
- `finrank <= 1` does not imply a nonzero defect or exact rank one.
- `g_N != 0` does not prove the defect functional is nonzero.
- same-space algebraic conjugation does not automatically preserve self-adjointness in the original inner product.
- use `A - lam I` for `lam < 0`; never assume `A⁻¹` for the semidefinite predecessor block.
- unique negative eigenline, scalar Schur/Feshbach closure, simultaneous-resonance exclusion, positivity, finite-to-infinite closure and RH remain OPEN unless separately theorem-backed.

## Living research records

- `research/RHRC/CURRENT_RESEARCH_PLAN.md`
- `research/RHRC/RESEARCH_LEADS.md`
- `research/RHRC/RESEARCH_LEADS_POST_110_DELTA.md`
- `research/RHRC/routes/R003_ccm_bridge/README.md`
- `research/RHRC/CLAIM_REGISTRY.json`
- `research/RHRC/R003_PROMOTED_BINDINGS.json`

**RH remains OPEN.**
