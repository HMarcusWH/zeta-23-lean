# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

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

Live GitHub head + exact Lean/compiler/CI remain authoritative. PR #140 is theorem-bearing and advances theorem authority beyond #137. It does **not** prove dense regular apertures, successor positivity, negative-root exclusion, or RH.

## Current theorem ladder

```text
off-line zeta zero
  -> legal finite canonical negative obstruction                     PROVED
  -> global first bad + both predecessor parities nonnegative        PROVED
  -> exact shell/KKT/Schur/secular machinery                         PROVED
  -> source-explicit transfer                                        PROVED / #129
  -> exact canonical source-moment decomposition                     PROVED / #131
  -> denominator-free zero-shift kernel/source transport             PROVED / #134
  -> scalar-sensitive absolute canonical source energy               PROVED / #136
  -> exact source pairing + one-step determinant                     PROVED / #137
  -> off-line zero => q_c<0 OR exists w, Delta(w)<0                  PROVED / #137
  -> every sufficiently large aperture has a finite negative
     canonical witness and a freshly selectable global first bad     PROVED / #140
  -> predecessor determinant !=0 <-> injective, with unique
     zero-shift preimage on a regular predecessor                    PROVED / #140
  -> frozen prime-cutoff equality, threshold atom vanishing,
     exact real-axis -log(L) scalar extraction                       PROVED / #140
```

No theorem proves unconditional `canonicalOneStepDomination`, dense regularity, the final regular Schur-energy sign, negative-root exclusion, or RH.

## Post-#140 route correction

The key new theorem is the aperture quantifier upgrade:

```text
off-line zero
  -> exists L0>0
  -> for every L>L0 there is a fresh finite negative canonical witness.
```

This means the A4R route can choose a convenient aperture first and obtain a finite witness there.

The preferred regularization strategy is now **one frozen cutoff cell**, not an all-size Baire construction.

Choose a large integer `Q` and work strictly inside

```text
log Q < L < log(Q+1).
```

On that cell `floor(exp L)=Q`, so the prime source is a fixed finite frozen sum. Invoke #140 at one interior aperture to get a finite negative witness `(N,u)`. Once `N` is known, continuity only has to preserve that one strict negative quadratic value, and determinant avoidance only has to cover the finite family

```text
p in {even,odd},  1 <= k <= N.
```

Then move to a nearby aperture in the same cell where those finitely many predecessor blocks are regular, keep the same negative witness, and **reselect** global first-bad there.

This removes three unnecessary primary obligations from the old plan:

- no countable all-size Baire theorem;
- no prime-threshold crossing during the regularizing move;
- no assumption that an old least-bad index persists.

## NOW — A4R1 fixed-cell finite regularization

The open theorem work is:

```text
fixed cutoff cell
  -> continuity of a fixed finite canonical quadratic value
  -> analytic/holomorphic representation of the actual projected predecessor
  -> determinant nonidentity for each fixed parity/size
  -> dense regular apertures for each fixed block
  -> finite simultaneous avoidance through a prescribed size M
  -> compose with #140 witness + fresh first-bad reselection.
```

The #140 scalar theorem already locks the real-axis identity

```text
-2*wCorrection(L) = -log(L) + remainder(L).
```

The remaining analytic difficulty is the full production predecessor, especially the archimedean channel. Existing `DictionaryArchPhysical.lean` and `DictionaryArchBridge.lean` are now resurrected as likely infrastructure for that continuation.

The log-lift/monodromy determinant argument remains a **LEAD**, not a theorem.

## After regularity — the decisive arithmetic obstruction

At the reselected first-bad state, predecessor nonnegativity comes from minimality. Regularity removes the kernel and gives a unique solution

```text
A x0 = b.
```

Let

```text
u0 = c - x0.
```

The intended regular countercertificate is

```text
Ecanonical(u0) = Re S0 < 0.
```

The decisive remaining arithmetic theorem is still

```text
Ecanonical(c-x0) >= 0
```

on that exact forced regular first-bad trial, equivalently in inverse shorthand

```text
<b,A^-1 b> <= q_c.
```

A proof that merely assumes successor positivity under another name is circular.

## Preserved research constraints

- **DERIVED:** under predecessor PSD and one-dimensional shell, universal `q_c>=0` plus `Delta(w)>=0` is equivalent to successor one-step positivity.
- **DERIVED:** `Delta(P_kerA b)=-||P_kerA b||^4`.
- **DERIVED / external exact-check:** `d=-(6/(2*N-1))a` for the two correction vectors.
- **DERIVED / external symbolic:** atomwise determinant positivity fails at the leading tested source-atom coefficient.
- **EXPERIMENTAL SIGNAL:** canonical Schur endpoints can be residues of extreme channel cancellation.
- **EXPERIMENTAL SIGNAL:** tiny modified prime-weight perturbations can flip successor sign while predecessors remain positive.

These constrain proof design; they are not RH evidence.

## Active path

```text
PROVED through #140
  eventual aperture freedom + regularity scaffold

NOW
  one frozen cutoff cell
  -> fixed-block analyticity/nonidentity
  -> finite simultaneous regularization
  -> preserve one finite negative witness
  -> fresh first-bad reselection

THEN
  regular first-bad countercertificate with unique A x0=b

DECISIVE OPEN THEOREM
  Ecanonical(c-x0) >= 0 on the exact forced regular trial

TARGET
  contradiction -> no off-line zero -> explicit Mathlib RH wrapper
```

Universal one-step domination remains a broad fallback if a genuinely independent positive canonical arithmetic mechanism is found.

## Permanent firewalls

- RH remains OPEN.
- theorem authority is through #140, not beyond it.
- aperture freedom is proved; dense regular-aperture selection is not.
- regularity is not successor positivity.
- a regular first-bad negative state is not yet a contradiction.
- source decomposition is not source positivity.
- no inverse notation is load-bearing before regularity; use the unique preimage theorem when formalizing.
- no factorwise division by unproved transfer/source quantities.
- D remains algebraic, not unitary/isometric.
- generic or modified-source countermodels do not refute the actual canonical source.
- external exact checks and numerical experiments are not theorem authority.
- machine claim promotion remains separate from compiler theorem validity.

## Living research records

- `research/RHRC/CURRENT_RESEARCH_PLAN.md`
- `research/RHRC/RESEARCH_LEADS_POST_140_APERTURE_FREEDOM_DELTA.md` — newest research-priority delta
- `research/RHRC/RESEARCH_LEADS_POST_138_ASTRA_DELTA.md` — historical pre-#140 delta
- `research/RHRC/external_reviews/ASTRA_POST_138_RH_PATH_ASSESSMENT_2026_09_09.md`
- `research/RHRC/countermodels/POST_138_ASTRA_DIAGNOSTICS_2026_09_09.md`
- `research/RHRC/OBSTRUCTION_LEDGER.md`
- `research/RHRC/DEAD_ROUTES.md`
- `research/RHRC/routes/R003_ccm_bridge/README.md`
- `research/RHRC/control_v2/README.md`

**RH remains OPEN.**