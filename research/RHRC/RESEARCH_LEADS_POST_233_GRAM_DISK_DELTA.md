# Post-#233 research leads delta — retained Gram disk

> **RH remains OPEN.**

## What became formally true

PR #233 is merged theorem authority.

Exact provenance:

- validated head: `565428e066004e559490fbe1d21d46ef14494de3`;
- merge commit: `9dfee4f50d5b57c92327da564ddf2f6159223fe1`;
- validated/merged tree: `5713b8d8088864cb126aae48a3a5a5ac8304807a`.

On the retained selected-even / odd-good branch, Lean proves the energy-form,
sharp, and outer cross-parity source Gram disks. It also proves the exact
shifted predecessor-resolvent energy identity and the good-sector canonical
Cauchy--Schwarz theorem.

The sharp retained constraint is

```text
|q - M4 + S*C|^2
  <= Ec * (Re(C) + lam * ||R a||^2),
lam < 0.
```

The outer consequence is

```text
|q - M4 + S*C|^2 <= Ec * Re(C).
```

## Workflow harvest

All 11 workflows attached to the validated #233 head completed green. The Lean
formal-validity job built the CCM and exceptional-zero trees and passed the
forbidden-placeholder/project-axiom gate. New declarations report only the
accepted foundational axioms `propext`, `Classical.choice`, and
`Quot.sound`.

The research-producing/regression workflows preserved their prior
classifications. In particular, the post-214 full-carrier sign-indefinite
result and post-222 zero-qualified-point bounded result were replayed rather
than promoted into new theorem authority.

## What changed

The retained source balance from #231 is no longer only an affine identity.
On the odd-good branch it now lies inside a theorem-locked canonical Gram
disk, including the exact negative-shift correction.

The successful proof also proves that
`canonicalOneStepDomination_of_not_parityBad` is a structural consequence of
sector goodness. It therefore cannot be counted as independent arithmetic
information in OBS-059I.

## Upstream implications

Audit hypotheses that simultaneously assume odd-sector goodness and
`canonicalOneStepDomination`; the latter can be removed as an independent
input.

The shifted-resolvent energy identity is parity-generic and can be reused
without taking an illegal zero-shift inverse or assigning a sign to a mixed
resolvent pairing.

## Downstream implications

The immediate question is whether the #233 disk actually shrinks the same
retained state after composition with the already-proved completed odd-secular
budget.

Write

```text
F = M4 - S*C,
B = (-lam) ||u_-||^2.
```

The theorem inventory gives

```text
B <= Re(star(S) F)
|q - F|^2 <= Rsharp.
```

The next target is therefore the exact disk/half-plane intersection. Its main
value is that the fourth moment `M4` cancels from the final necessary
condition.

## Resurrected routes

A higher Gram/determinant route remains viable only if it introduces a genuinely
new canonical observable. Another two-vector positivity theorem is consumed as
a default tactic by #233.

The canonical Pair-D route remains active. The generic C1 simultaneous-bad
countermodel remains valid and continues to require genuinely canonical
arithmetic information for exclusion.

## New RH-relevant clues

**LEAD / HYPOTHESIS:** the disk and secular half-plane compose to an
`M4`-free retained compatibility law:

```text
B <= Re(star(S) q)
OR
(B - Re(star(S) q))^2 <= normSq(S) * Rsharp.
```

Because `q=<c,c>` is positive real, the center projection is

```text
Re(star(S) q) = ||c||^2 Re(S).
```

This converts the next retained obstruction into a source-phase/radius
constraint with no fourth-moment variable.

## Falsification checks

The intersection theorem must remain denominator-free: no division by `S`,
`C`, `alpha`, `Gamma`, or shell energy.

The sharp radius must be proved before the outer radius is used.

The result must not be mislabeled as disk emptiness. It is only a necessary
compatibility condition.

Selected-even is not WLOG. Simultaneous odd-bad and odd-selected first-bad
remain open.

Any future claim that the compatibility law is impossible must be attacked by
synthetic Hermitian/PSD fixtures and by the existing #205/#215 counterexample
inventory before theorem investment.

## Highest-leverage next moves

1. Formalize the denominator-free complex disk/half-plane support lemma.
2. Compose it with #218/#219 and #233 on the exact retained state.
3. Eliminate `M4` from the final theorem statement.
4. Rewrite the shell-center projection as `||c||^2 Re(S)`.
5. After that theorem is compiler-green, test whether #213's exact canonical
   source kernel can violate or saturate the resulting compatibility law.

## Standing questions

Given everything now formally true, what becomes possible that was not
possible before?

If #233 contains an RH-relevant clue, does it propagate through the completed
secular budget by eliminating `M4` and shrinking the retained source state?

What experiment, lemma, reformulation, or connection most efficiently decides
whether the resulting disk/half-plane compatibility is genuinely restrictive?
