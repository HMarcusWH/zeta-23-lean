# Post-#234 research leads delta — disk/secular intersection

> **RH remains OPEN.**

## What became formally true

PR #234 is merged theorem authority.

Exact provenance:

- validated final head: `6d9b60752f7a4f164113bb0602fcdee87e2a54a1`;
- merge commit: `b18d81f11a04982e438b7e196853ae665dab0cc2`;
- validated/merged tree: `94a0db085c35d2aba753a8359e452e4189c5c897`.

On the selected-even / odd-good branch, Lean proves the sharp retained
disk/secular intersection and the real-source/radius alternative

```text
B <= ||shell||^2 Re(S)
OR
(B - ||shell||^2 Re(S))^2 <= normSq(S) Rsharp.
```

The final compatibility law is M4-free.

## Workflow harvest

All 11 workflows attached to the validated #234 head completed green. The Lean
job built CCM and ExceptionalZero and passed the no-placeholder/project-axiom
gate. The RHRC suite and Control-v2 smoke passed. Research replays preserved
their earlier dispositions; they did not become theorem authority.

The latest post-#165 scout attempted 672 finite states, retained 251 H1 margin
states, and found 0 shifted states. The checked-in post-#165 Arb replay
certified 0 shifted roots. This is research evidence about sampled scope only.

## What changed

PR #234 removes M4 from the retained selected-even / odd-good compatibility
law. The surviving variables are the exact source moment, shell norm, shifted
odd trial norm, sharp resolvent radius, and negative root.

This is state-space compression, not an arithmetic sign theorem.

## Upstream implications

The exact source moment can now be rewritten through PR #213 as
`quadraticNormalSourceKernelRHS`, so the remaining compatibility law can be
expressed directly in the canonical pole/arch/prime source kernel.

No division by the source moment or radius is required.

## Downstream implications

Define

```text
D = B - ||shell||^2 Re(S)
E = D^2 - normSq(S) Rsharp.
```

Then odd-good implies `D <= 0 OR E <= 0`. Therefore independent canonical
arithmetic proving `D>0` and `E>0` forces the odd successor to be bad.

This is the next theorem interface.

## Resurrected routes

The exact source-kernel lane from #211/#213 is now the primary route because
#234 gives it a compressed scalar target. Higher Gram geometry remains
secondary.

The numerical shifted-state lane remains useful, but only after matching
Lean's canonical cubic-shell normalization.

## New RH-relevant clues

**LEAD / HYPOTHESIS:** the selected-even / odd-good branch may reduce to
sign control of two explicit real scalars built from the canonical
continuous-plus-prime source kernel.

If both signs are eventually proved positive, the selected-even branch is
forced into simultaneous odd badness.

## Falsification checks

Do not infer `D>0` or `E>0` from #234 itself.

Do not use the arbitrary integer `exact_shell_generator` from the older
post-#165 diagnostic as if it were Lean's canonically normalized
`intrinsicCubicShellPart` for raw D/E magnitude comparisons.

The later numerical audit must use the exact canonical shell reconstruction
already available in the post-#222 geometry or an equivalent shared helper.

Do not reinterpret 672 attempted / 0 shifted states as a positivity theorem.

## Highest-leverage next moves

1. Formalize D and E directly with `quadraticNormalSourceKernelRHS`.
2. Prove odd-good implies `D<=0 OR E<=0`.
3. Expose the contrapositive theorem `D>0 AND E>0 -> odd-bad`.
4. Keep #117 control semantics and #223 research evidence fixed.
5. Only then decide whether the next move is analytic sign control or a
   canonical-normalized shifted-state audit.

## Standing questions

Given everything now formally true, what becomes possible that was not
possible before?

Can actual canonical source arithmetic force both D and E positive?

If it can, does the resulting simultaneous-bad branch admit a separate
canonical exclusion?

What is the cheapest falsification test for either proposed sign before
investing in a global theorem?
