# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

## Current authority snapshot

```text
THEOREM AUTHORITY
latest theorem-bearing PR = #182
validated theorem head = 0c3f63cdc4774ba1a68b21d1558ea0ee860a938d
merged theorem commit = a69160d37a84049711aaff6c3d5db804583a7306
validated theorem tree = e0b260b3b3a1ed470d54c14d8c0c46b32379f3fb
RHRC #1082 = SUCCESS
Permansson #855 = SUCCESS

LATEST RESEARCH-EVIDENCE ANCHOR
merged research PR = #180
validated research head = a87469da9e611b53ae400cb4b18ce4afeb94e6d2
merged research commit = 93ea3df51f2671e316197c1530ea504dee76e821
research tree = 8199cdc543f1b761c70466dfd602c143a277e6a2
RHRC #1077 = SUCCESS
Lean #837 = SUCCESS
Permansson #850 = SUCCESS

CONTROL SEMANTIC AUTHORITY
PR #117 merge = 19346f4c00d13bf33db95cbe5325233f86e54c12
selected formal first break = E4A4-SCHUR-FB-05
RH = OPEN
```

## Theorem-backed route

```text
finite negative obstruction / first-bad / Schur machinery            PROVED
source-explicit cross-parity transfer                                 PROVED / #129
exact canonical source-moment decomposition                           PROVED / #131
zero-shift transport / absolute energy / determinant                  PROVED / #134-#137
regular selected first bad                                            PROVED / #140-#150
retained certificate + exact pole-prime discrepancy                   PROVED / #153
legal generic Riesz smoothing + source parity/even jets               PROVED / #155
complex production transport + exact complete Riesz 6/even 8          PROVED / #157
retained transformed negativity + ExceptionalZero R6 wrapper          PROVED / #157
general moment-prefix odd-jet law                                     PROVED / #159
same-state shifted Riesz x cross-parity source composition            PROVED / #161
mixed quadratic-normal seventh source jet -> M4                       PROVED / #163
finite-prime sampling of the same mixed source observable             PROVED / #163
mixed-jet squared Riesz-8/Riesz-9 boundary coupling                   PROVED / #163
generic real 2x2 Schur-envelope derivative                            PROVED / #182
H1 contact determinant/pivot orientation equivalence                  PROVED / #182

source-moment / M4 global rigidity                                    OPEN
endpoint-scalar global sign/nonvanishing                              OPEN
production/Hermitian Schur-envelope bridge                            OPEN
production remainder/contact-orientation bound                        OPEN
q13 finite-width H1 / whole-cell sign-contact classification          OPEN / ACTIVE
simultaneous even/odd bad exclusion                                   OPEN
odd-selected branch closure                                           OPEN
negative-root exclusion                                               OPEN
terminal zeta/Mathlib seam                                            OPEN
RH                                                                    OPEN
```

## What #182 changes

For

```text
H = [[a,b],[b,d]]
P = d - b^2/a
Delta_2 = a*d-b^2
```

Lean now proves the exact envelope derivative and its determinant-quotient equivalent:

```text
P' = d' - 2*(b/a)b' + (b/a)^2 a'
Delta_2' = a'P + aP'.
```

At `P=0`,

```text
Delta_2' = aP'.
```

Under H1 `a>0`, determinant and pivot derivative signs agree. This is generic calculus only; no zeta-arithmetic sign is established.

## Research state through #180

The q13/N2/K3/even finite microscope has validated value and derivative infrastructure. #180 gives exact-center orientation:

```text
POINT_DERIVATIVE_BASIN_BRACKETED
MINIMUM_ORIENTED
left centers:  3/3 Delta_2' < 0
right centers: 3/3 Delta_2' > 0
```

but the nonzero-width primary Schur boxes are

```text
SCHUR_OUT_OF_H1_SCOPE
applicable_primary_count = 0.
```

So #180 does not prove finite-width Schur sign recovery or width gain.

## Immediate frontier — FB-05

### Finite lane

```text
1. point a(L0)>0 + rigorous a'(I) -> centered H1 enclosure
2. if H1 recovered, retry the #182-backed Schur derivative graph
3. if still unresolved, add Delta_2'' and centered mean-value/Taylor propagation
4. only after signed neighborhoods, use interval Newton/Krawczyk
```

### Formal Pair-A lane

The fixed-cell theorem inventory already proves source decompositions of the form

```text
M_Q(L) = -log(L) I + R_Q(L).
```

The next formal target is a normalization-safe production/Hermitian Schur-envelope theorem exposing

```text
P'(L) = -||u_L||^2/L + production remainder drift.
```

Then seek/falsify a source-specific contact-local bound that forces an orientation incompatible with first-bad crossing.

## Production normalization firewall

The q13 research integer shell generator spans the same one-dimensional shell as Lean's canonical cubic shell but is not theorem-identified with the same magnitude. Production is complex Hermitian while #182 is real 2x2. Do not silently identify those coordinate systems or replace `|b|^2/a` by `b^2/a` without a theorem.

## Current execution priority

1. centered H1 recovery on the frozen #180 boxes;
2. theorem-backed Schur-box retry only inside certified H1;
3. cheap numerical/interval split of universal log drift versus arithmetic remainder drift;
4. invariant/Hermitian production envelope theorem;
5. source-specific contact-local remainder bound only if the split survives falsification;
6. compose the resulting independent restriction with the exact retained state;
7. preserve `RH_OPEN` until the complete negative-root and terminal seams are theorem-backed.

Newest research synthesis:
`RESEARCH_LEADS_POST_182_SCHUR_ENVELOPE_CONTACT_ORIENTATION_DELTA.md`.

**RH remains OPEN.**
