# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

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

PR #138 is documentation/control synchronization only. Theorem authority remains through #137.

## Recent theorem packages

```text
#129 source-explicit cubic defect + exact cross-parity secular transfer
#131 exact canonical source-moment decomposition
#134 denominator-free whole-kernel source transport + direct zero-shift transfer
#136 absolute canonical source energy + scalar-sensitive production decomposition
#137 exact source pairing + one-step determinant + global sign-failure endpoint
```

## Current frontier after the post-#138 Astra audit

```text
A4b1 absolute canonical source energy                            PROVED / #136
A4b2a one-step determinant/sufficiency reduction                 PROVED / #137
A4R   regular-aperture/log-lift witness selection                OPEN / NOW
A4b2r regular minimizing-trial Schur-energy sign                 OPEN / AFTER A4R
A4b2b universal shell/determinant domination                     OPEN / BROAD FALLBACK
global first-bad exclusion                                       OPEN
terminal Mathlib RH wrapper                                      OPEN
RH                                                               OPEN
```

## Why the ordering changed

Post-#137 documentation already warned that universal domination was close to successor positivity. The Astra audit sharpens this to the derived equivalence, under predecessor PSD and a one-dimensional shell,

```text
q_c >= 0 AND forall w, Delta(w) >= 0
  <-> successor quadratic form >= 0.
```

That makes universal A4b2b an exact but not smaller positivity target.

A4R is now promoted because it attempts to remove only predecessor singularity/resonance by nearby-aperture witness selection. Generic regular negative examples show this does not imply successor positivity, so the reduction has independent information value.

## Intended A4R theorem shape

```text
strict finite canonical negative witness
  -> arbitrarily nearby aperture preserving negativity
  -> finitely many relevant predecessor blocks in both parities injective
  -> reselect global first-bad at the new aperture
  -> both predecessor blocks positive definite.
```

Candidate mechanism: frozen-cutoff `M_Q(L)=-log(L)I+B_Q(L)`, log lift `L=exp(z)`, periodic remainder, determinant nonidentity by finite characteristic-polynomial root count.

Required gates include exact scalar coefficient, frozen-cutoff analyticity, physical threshold continuity, fixed-basis/Gram correctness, simultaneous finite avoidance, preservation of negativity, fresh first-bad reselection, and predecessor-compression identification.

## After A4R

Regularity gives a unique preimage

```text
x0 = A^-1 b
u0 = c - A^-1 b
```

and the forced bad state satisfies

```text
Ecanonical(u0) = Re S0 < 0.
```

The decisive arithmetic problem is then the scalar inequality

```text
Ecanonical(c - A^-1 b) >= 0
```

or equivalently `<b,A^-1b> <= q_c`, derived from the exact canonical prime/arch/scalar interaction rather than a positivity restatement.

## Research constraints preserved

- `Delta(P_kerA b)=-||P_kerA b||^4` gives an explicit resonant determinant witness — DERIVED.
- A root-selected predecessor vector at the safe negative root has an exact derived determinant formula.
- The audit reports `d=-(6/(2*N-1))a` for the two correction vectors — DERIVED/external exact-check, not Lean-locked.
- Atomwise determinant positivity is disfavored by a reported negative leading source-atom determinant coefficient.
- Canonical Schur energies can be extremely cancellation-sensitive in sampled high-precision cases.
- Tiny modified prime-weight perturbations can flip successor sign while predecessors remain positive; exact arithmetic coefficients matter.

## Firewalls

- RH remains OPEN.
- #137 domination sufficiency is conditional.
- regularity is not successor positivity.
- the regular scalar sign theorem is not proved.
- external exact checks and numerics are not theorem authority.
- no zero-shift inverse before regularity is established.
- no termwise source-atom positivity shortcut.
- no factorwise division by unproved transfer quantities.
- D remains algebraic, not unitary/isometric.
- machine claim promotion remains separate.

Newest research detail: `research/RHRC/RESEARCH_LEADS_POST_138_ASTRA_DELTA.md`.

**RH remains OPEN.**