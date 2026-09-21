# Post-#235 research leads delta — source-kernel forbidden quadrant

> **RH remains OPEN.**

## What became formally true

PR #235 merged green with validated head
`d7ae288e874b2cf3462a8e00c35c7b713607a192`, merge commit
`0c347a99a02157798109ffb5a4718e201e6fa083`, and exact validated/merged
tree `ba6d8e6f5a714742353678e36cbc90d869b31798`.

On the selected-even / odd-good retained state Lean proves, for the exact
source-kernel observables D and E,

```text
D <= 0 OR E <= 0.
```

Equivalently,

```text
D > 0 AND E > 0 -> odd successor ParityBad.
```

No strict sign of D or E is proved.

## Workflow harvest

All 11 attached workflows on the validated #235 head completed green. The main
formal-validity workflow built CCM and ExceptionalZero, ran the RHRC/control
suites, and passed the forbidden-placeholder/project-axiom gate. Research
replays preserved their earlier classifications and did not become theorem
authority.

## What changed

The selected-even / odd-good obstruction is now an exact forbidden-quadrant
problem for two real observables built from the canonical source kernel.

The post-green proof read exposed a new structural opportunity: the retained
negative-root trial is canonically cubic-normalized with quotient coordinate
one, while the canonical finite matrix has real entries. This may eliminate
the otherwise free complex phase.

## Upstream implications

The canonical matrix is definitionally `cutoffFreeMatrix`, whose entries are
real scalars cast into `ℂ`. Existing E3-A machinery proves that any genuine
negative eigenmode canonically normalizes to `cubicSecularTrialVector` and
that this trial has cubic quotient coordinate one.

This makes conjugation-compatible canonical normalization the smallest upstream
lemma set worth formalizing next.

## Downstream implications

If the retained trial is fixed by coordinate conjugation, then the exact source
kernel is real and

```text
normSq(S) = (Re S)^2.
```

Writing `s = Re S`, #235 becomes

```text
D <= 0 OR D^2 <= s^2 Rsharp.
```

The complex source geometry would therefore collapse to one real source scalar.

## Resurrected routes

The old intuition "the matrix is real, so use a real eigenvector" was
previously insufficient because eigenvector phase was arbitrary. The canonical
cubic quotient normalization now supplies the missing phase anchor, so the
route is reclassified as worth formalizing.

## New RH-relevant clues

**LEAD / HYPOTHESIS:** canonical conjugation plus quotient normalization one
forces the selected-even retained trial to be real.

If true, the next arithmetic obstruction is one-dimensional in the source
coordinate rather than genuinely complex.

## Falsification checks

Hermitianity alone does not select a real phase. The proof must use real matrix
entries, conjugation stability of the constrained carrier, and canonical cubic
normalization.

No eigenvalue-simplicity assumption may be introduced.

The real-phase theorem, even if proved, does not imply `s>0`, `D>0`, or
radius-gap positivity.

## Highest-leverage next moves

1. Prove conjugation stability of the parity carrier and compressed canonical
   operator.
2. Prove the canonical cubic quotient coordinate conjugates correctly.
3. Use existing normalized-eigenmode uniqueness to fix the retained phase.
4. Rewrite the exact source moment through its finite matrix representation to
   prove source-kernel reality.
5. Collapse #235 to the one-real-source scalar inequality.

## Standing questions

Given everything now formally true, what becomes possible that was not
possible before?

Does canonical quotient normalization really remove the full complex phase?

Once the source is real, which exact pole/arch/prime inequality can most
cheaply falsify or prove the remaining one-dimensional compatibility law?
