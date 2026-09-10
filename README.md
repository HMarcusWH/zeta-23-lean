# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

## Current authority snapshot

```text
live main after merged PR #142 = 3e8d2995a1c00a9aef0d8cb0f5382658c91a8673
live main tree = a92d03d0d4ad800d544a835b8ae2e3d23bae2c47

theorem-state anchor = PR #142 merge 3e8d2995a1c00a9aef0d8cb0f5382658c91a8673
validated theorem head = 23d96af9aafd86ad26ae7913c3d6c14503d539de
validated theorem tree = a92d03d0d4ad800d544a835b8ae2e3d23bae2c47
RHRC #889 = SUCCESS
Permansson #662 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

Live GitHub head + exact Lean/compiler/CI remain authoritative. PR #142 is theorem-bearing and advances theorem authority beyond #140. It does **not** prove determinant nonidentity, dense regular apertures, successor positivity, negative-root exclusion, the final regular Schur-energy sign, or RH.

## Current theorem ladder

```text
off-line zeta zero
  -> legal finite canonical negative obstruction                     PROVED
  -> global first bad + predecessor parity nonnegativity              PROVED
  -> shell/KKT/Schur/secular machinery                               PROVED
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
  -> actual canonical source entries and fixed-vector energy are
     continuous on one physical cutoff cell                          PROVED / #142
  -> same finite size and same vector remain strictly negative on
     an open neighborhood inside that cutoff cell                    PROVED / #142
  -> off-line zero supplies such a locally persistent witness at
     every chosen sufficiently large cell-interior aperture          PROVED / #142
```

No theorem proves dense regularity, determinant nonidentity, the regular first-bad arithmetic sign, negative-root exclusion, or RH.

## Post-#142 route correction

The preferred regularization problem is now smaller than the post-#140 finite-prefix plan.

For a physical cutoff cell

```text
I_Q = (log Q, log(Q+1)),
```

define the least bad size over the **entire cell**:

```text
K* = min { K | exists L in I_Q, AnyParityBad L K }.
```

This is currently a **DERIVED** composition, not a merged theorem. Its key consequence is that every smaller size is nonnegative in both parities throughout the whole cell. If `N*=K*-1`, the predecessor sector at the cell-minimal bad size is therefore PSD across the cell.

Choose a bad parity witness at some `L*`. PR #142 preserves that same witness on an open `J subset I_Q`. Dense regularity for the relevant predecessor determinant would then allow selecting `L2 in J` where the same negative witness survives and the predecessor is injective; PSD + injective gives positive definiteness in finite Hermitian dimension.

So the primary route no longer needs either:

- countable all-size Baire regularization; or
- simultaneous regularization of every size through a finite prefix.

Both remain fallbacks if the smaller production theorem fails for a theoremized reason.

## NOW — analytic frozen predecessor regularity

The open theorem work is:

```text
fixed physical cutoff cell
  -> production cell-minimal bad-state wrapper
  -> complex continuation of the actual frozen intrinsic predecessor
  -> exact split A(L) = -Log(L) I + B(L)
  -> single-valued holomorphic remainder on a punctured domain
  -> logarithmic monodromy / finite-spectrum determinant nonidentity
  -> dense regular apertures
  -> intersect density with the #142 persistent-negative open set
  -> regular first-bad countercertificate.
```

PR #142 makes the analytic step more concrete by replacing the apparent archimedean origin singularities with continuous divided-slope regularizations. After the real change of variables `x=L t`, the production integrals have fixed interval `[0,1]` and fixed oscillatory frequency. Those rescaled formulas are **DERIVED**, not merged Lean declarations.

The log-lift determinant argument remains a **LEAD / HYPOTHESIS** until the actual production remainder is theoremized on a domain that supports winding around zero without hidden monodromy cancellation.

## After regularity — the decisive arithmetic obstruction

At a regular first-bad state, cell/global minimality gives predecessor nonnegativity and regularity gives a unique solution

```text
A x0 = b.
```

Let

```text
u0 = c - x0.
```

Existing #136 Schur/energy machinery supplies the target negative regular certificate

```text
Ecanonical(u0) = Re S0 < 0
```

once the regular selection is formally packaged.

The decisive remaining arithmetic theorem is still

```text
Ecanonical(c-x0) >= 0
```

on that exact forced production state, equivalently after regularity

```text
<b,A^-1 b> <= q_c.
```

A proof that merely repackages successor positivity or universal one-step domination is circular.

## Stronger falsification after #142

A generic analytic centered diagonal family can simultaneously have:

```text
an explicit -log L scalar term;
predecessors positive for all L>0;
persistent negative finite witnesses at every aperture;
a globally minimal bad size;
common negative behavior in both parities.
```

Therefore

```text
aperture freedom + persistence + minimality + regularity + parity + scalar log
```

does **not** force a contradiction by generic geometry alone. The actual canonical pole/archimedean/von-Mangoldt arithmetic must do new work.

See `research/RHRC/countermodels/POST_142_REGULARIZATION_COUNTERMODEL_2026_09_10.md`.

## Active path

```text
PROVED through #142
  eventual aperture freedom
  + regularity/frozen-source scaffold
  + fixed-cell canonical continuity
  + same-witness local persistence

NOW
  production cell minimum
  + analytic frozen predecessor
  + determinant nonidentity
  + dense fixed-cell regularity

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
- theorem authority is through #142, not beyond it.
- fixed-cell continuity and witness persistence are PROVED; analyticity and dense regularity are OPEN.
- cell-minimality and the smaller regularization composition are DERIVED until formally packaged.
- regularity is not successor positivity.
- a regular first-bad negative state is not yet a contradiction.
- source decomposition is not source positivity.
- no inverse notation is load-bearing before regularity; use the unique-preimage theorem when formalizing.
- no factorwise division by unproved transfer/source quantities.
- D remains algebraic, not unitary/isometric.
- generic or modified-source countermodels do not refute the actual canonical source.
- external exact checks and numerical experiments are not theorem authority.
- machine claim promotion remains separate from compiler theorem validity.

## Living research records

- `research/RHRC/CURRENT_RESEARCH_PLAN.md`
- `research/RHRC/RESEARCH_LEADS_POST_142_FIXED_CELL_PERSISTENCE_DELTA.md` — newest research-priority delta
- `research/RHRC/RESEARCH_LEADS_POST_140_APERTURE_FREEDOM_DELTA.md` — historical pre-#142 delta
- `research/RHRC/RESEARCH_LEADS_POST_138_ASTRA_DELTA.md` — historical pre-#140 delta
- `research/RHRC/countermodels/POST_142_REGULARIZATION_COUNTERMODEL_2026_09_10.md`
- `research/RHRC/OBSTRUCTION_LEDGER.md`
- `research/RHRC/DEAD_ROUTES.md`
- `research/RHRC/routes/R003_ccm_bridge/README.md`
- `research/RHRC/control_v2/README.md`

**RH remains OPEN.**