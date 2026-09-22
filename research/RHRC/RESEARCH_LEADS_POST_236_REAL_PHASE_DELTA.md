# Post-#236 research leads delta — retained canonical real phase

> **RH remains OPEN.**

## What became formally true

Merged PR #236 is theorem authority at validated head
`45491342f5661429679579c7889c1ad8b96728b6`, merge commit
`a66e1c617033f4adaa52e935668399efb93048ac`, tree
`5ef597b1d75075ec2299261a4193432a36932ffe`.

The retained selected-even negative-root trial is fixed by canonical coordinate
conjugation. Consequently the exact retained production source moment and source
kernel are real. Writing `s = Re S`,

```text
star S = S
Im S = 0
normSq(S) = s^2
D <= 0 OR D^2 <= s^2 Rsharp
D > 0 AND s^2 Rsharp < D^2 -> odd successor ParityBad
```

No sign of `s`, no sign of `D`, no sharp-radius gap, no simultaneous odd-bad
exclusion, no odd-selected closure, no parity-complete retained-state exclusion,
and no RH theorem is proved.

## Workflow harvest

All 13 attached checks completed green on the exact #236 head.

- **FORMAL VALIDITY GATE:** Lean built `Zeta23.CCM`; the promoted #236 theorem
  declarations print only the accepted standard axioms and no `sorryAx`.
- **REGRESSION GATES:** RHRC Python/control, R003 normalization audit, Permansson,
  and the frozen historical replays passed.
- **RESEARCH-PRODUCING CHECKS:** the historical outputs remain claim-capped.
  Post-200 finishes `DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED` with
  `NO_UNIQUE_PRIMARY_LOCK`; post-202 preserves
  `COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED`; post-214 preserves full-space dual
  independence together with full-space sign indefiniteness; post-222 preserves
  `NO_FROZEN_CELL_MINIMAL_BIREGULAR_STATE_CERTIFIED`.

None of those replay outcomes is promoted to theorem authority.

## What changed

The retained source no longer has a free complex phase. The post-#235 forbidden
quadrant has become a one-real-scalar radius compatibility problem. Reading the
successful proof also exposes a stronger composition that #234 had deliberately
eliminated: return to the exact completed source `M4 - S*C` before eliminating
`M4`, and use the new reality information to scalarize that whole object.

The existing theorem inventory already gives `star C = C`, `Re C >= 0`,
nonzero canonical odd secular trial, and nonzero cubic shell. Therefore the
remaining upstream reality lemma for `M4` should be small.

## Upstream implications

The next smallest theorem layer is:

```text
retained trial real
  -> raw retained coefficients conjugation-fixed
  -> retained M4 real
  -> S, M4, C all real
  -> completed source F = M4 - S*C real
```

No new eigenvalue-simplicity or normalization assumption should be introduced.

## Downstream implications

Write

```text
s = Re S
m = Re M4
c = Re C
f = m - s*c
B = (-lambda)||u_-||^2
q = ||shell||^2
R = Rsharp
```

On selected-even / odd-good, the existing exact theorems should reduce to

```text
B > 0
q > 0
c >= 0
B <= s*f
(q-f)^2 <= R
B + s^2*c <= s*m
D <= s*(f-q)
```

This is the target theorem family `RETAINED_REAL_COMPLETED_SOURCE_CORRIDOR`.

## Resurrected routes

The old completed-source geometry is worth revisiting because #236 supplies a
prerequisite that did not exist when #234 eliminated `M4`: the retained source
phase is now canonical and real. This is a dependency change, not a re-run of the
same complex disk/half-plane argument.

The post-202 composite parity-gap mechanism is not resurrected; its predeclared
pattern remains falsified. Universal full-carrier source-sign arguments remain
quarantined by post-214 sign indefiniteness.

## New RH-relevant clues

**LEAD / HYPOTHESIS:** if independent canonical arithmetic proves

```text
Rsharp <= q^2
```

then the real corridor forces `s > 0`. Indeed `B > 0` and `B <= s*f`
force `s` and `f` to have the same nonzero sign; if both were negative then
`q-f > q > 0`, contradicting `(q-f)^2 <= Rsharp <= q^2`.

That would also force `f > 0` and, using the existing source/M4 orientation,
`m > 0`.

This barrier is not proved by #236 and must remain OPEN until theorem-backed.

## Falsification checks

Before treating the shell-radius barrier as a route:

- check the degenerate cases `s=0`, `f=0`, `Rsharp=0`;
- check the tangent case `Rsharp=q^2`;
- verify no hidden use of the desired source sign occurs in the derivation;
- preserve the exact negative-shift correction in `Rsharp`;
- do not replace the retained-state claim with a full-carrier universal sign;
- test whether known bounded fixtures admit `Rsharp>q^2` before promoting the
  barrier as a plausible global theorem.

## Highest-leverage next moves

1. Formalize retained `M4` reality from #236 conjugation-fixed normalization.
2. Scalarize the exact completed-source budget and sharp Gram disk.
3. Prove the strict structural facts `B>0`, `q>0`, and `c>=0`.
4. Package the real semialgebraic corridor and the conditional
   `Rsharp <= q^2 -> s>0` interface.
5. Only after that theorem layer is green, attack whether the retained canonical
   state actually satisfies the shell-radius barrier or the stronger direct
   #236 contradiction inequalities.

## Standing questions

**Given everything now formally true, what becomes possible that was not
possible before?** The exact completed source can now plausibly be reduced from
complex geometry to real scalar algebra without discarding `M4`.

**If this contains a clue toward RH, where does it propagate?** A genuine
retained-state radius barrier would orient the source and completed source,
tighten the #235/#236 deficit geometry, and may eliminate the selected-even /
odd-good branch.

**What experiment, lemma, reformulation, or connection most efficiently tests
the clue?** First theoremize the real completed-source corridor; then test/prove
`Rsharp <= q^2` on the exact retained state rather than another ambient source
decomposition.
