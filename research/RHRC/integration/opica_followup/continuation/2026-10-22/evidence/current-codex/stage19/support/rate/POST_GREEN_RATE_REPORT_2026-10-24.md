# OPICA arithmetic window prerequisites — 24 October 2026

Base commit: `59ff485551771c0ab6322562d18fb8e9d4166da4`.
Base tree: `396665de3d14c2db60a4a85c646dd56d718f07ff`.
The repository worktree was clean when the narrow receipt was sealed. The six
compiled audit files live outside the repository in `work/audit-rate`; they are
supporting research, not promoted original primary roots or a release receipt.
RH, Step 4, J5.2, MS1 and full aggregate acceptance remain OPEN.

The immutable receipt is `RATE_SUPPORT_RECEIPT_2026-10-24.json`, SHA-256
`53816edd71989064e592a44b598a5894b961a55d767acf804d1cdf0327d6980b`.
It records six directly observed exit-0 compiler processes, thirty printed
transitive axiom audits, compiler/pin/object/log/source hashes and 264 imported
project-source dependency files. All audited closures use only `propext`,
`Classical.choice`, `Quot.sound`. The independent expected-type files are separately
compiled and expand the physical integrals and max-floor index. They do not
constitute independent human mathematical review. The receipt is not a cold
rebuild of every imported source by this subagent and is not the full repository
compiler exporter. The root agent separately rebuilt the current auxiliary,
multiplicity-tail and native-window modules after detecting stale older objects.

## 1. What became formally true

Write `Theta = nativeZeroDisplacementSup`, `K_d = nativeFieldOrderConstant d`,
`alpha_k = k+1/2`, `A_k = auxCompletionBound k`, and

\[
 E_{d,C}(T)=\int_{T-C\log T}^T |F_d(t)|^2\,dt.
\]

Here every field, source and completion is the existing literal native
construction. For all natural `d`, real `C≥0`, `T≥1` and `T−C log T≥0`, Lean proves

\[
 E_{d,C}(T)\le C\log T\,K_d^2e^{2\Theta T}.
\]

For every `alpha≥0`, the actual early weighted memory satisfies

\[
 J^{old}_{\alpha,d,C}(T)
 \le T K_d\exp(\Theta T-(\alpha+\Theta)C\log T).
\]

Its prefactor is polynomially weaker than the paper's
`K_d/(alpha+Theta)` and has the required same exponential separation. The
exact memory split `J = Jold + Jwin` and the physical Cauchy–Schwarz bound

\[
 (J^{win}_{\alpha,d,C}(T))^2\le C\log T\,E_{d,C}(T)
\]

also compile. This prefactor is weaker than `1/(2alpha)` and is sufficient for
logarithmic rates. The proof does not assume global square integrability of `F_d`.

Combining these facts with the existing exact A6 gives the following finite
horizon restriction. For every actual right zero `rho`, its full actual
multiplicity, every `d≥0`, and every completion index `k≥1`, put `p=rho−1/2`,
`delta=Re p`, `D = nativeMultiplicityTailConstant d rho`,
`r = auxRationalFactor k p`, `y = nativeAuxiliaryStableVector k d`, and

\[
 L=\frac{\sqrt{2\alpha_k}}{A_k}
      [D|r|e^{\delta T}-\|y\|]_+,
 \qquad
 O=T K_d e^{\Theta T-(\alpha_k+\Theta)C\log T}.
\]

Then Lean proves, with those exact source-specific quantities,

\[
 \boxed{[L-O]_+^2\le C\log T\,E_{d,C}(T).}
\]

The restriction yields a positive energy lower bound only when `L>O` and the
window length is positive. When `L≤O`, its left side is zero. When the completed
input dominates `D|r|e^(delta T)`, even `L` is zero. No positivity threshold was
silently discarded.

The source-cost lane proves, for every actual right zero, a fixed `Cp>0` such that

\[
 |\log |J_d(p)||\le C_p(d+1).
\]

For every positive cofinal real horizon schedule and arbitrary integer orders
with the original `d_n log(d_n+2)/T_n → 0`, both the signed source logarithm
divided by `T_n` and `log(1+K_(d_n))/T_n` tend to zero. The necessary order-zero
correction is explicit:

\[
 (d+1)\log(d+2)\le2d\log(d+2)+\log2.
\]

The original MS1 premise was not strengthened to `(d+1)log(d+2)=o(T)`.

The completion lane defines exactly
`k(T)=max(1,floor(xi T/log T))`. For all fixed `xi≥0`, Lean proves the rounding
bound by one, `k log T/T→xi`, `alpha_k log T/T→xi`, `k/T→0`, and, for each real
`Cp` and positive epsilon, eventually

\[
 \frac{k\log(k+1)+C_p(k+1)}T<\xi+\epsilon.
\]

The last upper asymptotic bound is exactly what the A5 lower estimate needs;
the separate exact limit of `log(k+1)/log T` is unnecessary.

## 2. Workflow harvest

These are local formal-validity checks, not GitHub jobs:

| Source or consumer | Authoritative successful log | Disposition |
|---|---|---|
| `RateSourceCosts.lean` | `source-cost-attempt5.log` | six supporting theorems, standard axioms |
| `ExpectedSourceCosts.lean` | `expected-source-cost-final.log` | three independently stated types and two mathematical controls |
| `RateWindowBounds.lean` | `window-bounds-attempt2.log` | actual energy and old-memory bounds; one harmless tactic-style warning |
| `RateCompletionIndex.lean` | `completion-cost-final.log` | actual continuous max-floor normalization costs, standard axioms |
| `RateMemoryWindow.lean` | `memory-barrier-attempt1.log` | exact split, Cauchy–Schwarz and full-multiplicity native energy barrier |
| `ExpectedWindowPrerequisites.lean` | `expected-window-attempt1.log` | six expanded types and two mathematical controls |

All preceding failed or intermediate logs are preserved. In particular the
misleadingly named early `source-cost-final.log` is a failed attempt; the sealed
receipt explicitly selects `source-cost-attempt5.log`. No failed process is
reported as green. No GitHub workflow authority is asserted by this lane; the
root task owns the complete workflow harvest and the full current-source replay.
The audit imports and compiler objects have their exact hashes in the receipt.
The source files, successful logs and receipt listed above are sealed unchanged.

## 3. What changed

At the audited starting source, `NativeWindowRate.lean` supplied the literal
energy, nonnegativity and pre-gap zero lemmas plus strict exponent feasibility.
The multiplicity module supplied A6 but did not yet consume it on the terminal
window. The new supporting proofs connect actual A6 to actual terminal energy
and discharge both-sign moving-source and completion-index accounting costs.
No original full-rate theorem was replaced by these proper supporting statements.
All `d≥0`, arbitrary zero multiplicity, continuous real horizons and the exact
positive-part subtraction survive. In particular no synthetic energy field,
caller-supplied window-rate premise, new axiom or zero-exclusion premise appears.

## 4. Upstream implications

The logarithmic source-factor identity and uniform raw-budget estimate are enough
to price MS1 under its original premise. Order zero contributes a fixed `log 2`
that disappears only after division by a cofinal horizon. The completion proof
needs only an upper asymptotic A5 cost, compressing the originally anticipated
floor/log proof graph. The two polynomially weaker memory estimates remove the
need for a sharp exponential antiderivative or sharp weighted Cauchy–Schwarz
constant when the target is only a logarithmic rate.

## 5. Downstream implications

The finite-horizon barrier excludes any hypothetical right-zero/source/window
configuration whose measured native energy is below the displayed positive
barrier. This is a real source-specific restriction, but it does not show that
the actual native energies violate it. The remaining J5.2/MS1 composition can
use precisely the same barrier and costs. A source-independent abstract
positive-energy envelope would not substitute for this native theorem.

## 6. Resurrected routes

The multiplicity tail → terminal energy route is now reduced to asymptotic
composition rather than new convolution or multiplicity machinery. A common
proof along arbitrary cofinal real horizons and slow source orders could yield
fixed source as a constant-order corollary. This should be done through genuine
source definitions with the frozen public contracts and dependency order retained.
The historical homogeneous spectral and raw-real-sampling routes are unaffected;
the separate sample-sign audit explains their existing obstruction.

## 7. New RH-relevant clues

DERIVED: if the A6 leading term survives its input subtraction and dominates
early memory at a controlled exponential rate, the actual terminal energy
inherits that rate. The paper's strict choice
`(Theta−delta)/(C−1)<xi<delta−b` is already available in the source and supplies
the required gap between `Theta−C xi` and `delta−xi`.

LEAD: the most informative obstruction is now quantitative native suppression
of the complete terminal energy or of the complete retained observation. An
upper bound for a discarded contrast alone still does not contradict this
barrier. No subexponential native energy upper bound or independent closing
inequality has been obtained here. The results are classical growth, floor and
Cauchy–Schwarz mechanisms combined with source-specific previously formalized
A6; no world-priority claim is made.

## 8. Falsification checks

Four theorem-backed controls compile separately:

1. Dropping the `log 2` correction makes the pointwise order-cost estimate false
   at `d=0`.
2. The actual source vanishes at both elementary parameters `p=±1/2`, so a
   global nonzero lower-cost assertion cannot silently replace the actual
   right-zero hypothesis.
3. Negative damping makes the exponential memory weight exceed one, invalidating
   the weight-dropping step. The theorem explicitly requires nonnegative damping.
4. If early memory dominates the A6 lower expression, the positive-part barrier
   is exactly zero. The result therefore cannot be read as unconditional positive
   energy at every horizon.

Further direct proof inspection: every zero hypothesis is conditional; the
existence of a right zero is not asserted or assumed globally. The unconditional
source/envelope accounting uses no no-zero premise. The barrier handles all
actual multiplicities through the native `D` and makes no simplicity assumption.
The zero-displacement case has no fictitious right-zero witness. Its full rate
must be closed by the upper estimate and nonnegativity, separately.

## 9. Highest-leverage next moves

1. Price the logarithm of the actual multiplicity-tail constant from its literal
   source-factor formula, and the actual stable input relative to `|r_k(p)|`.
2. Use the sealed A5 completion upper-cost bound, source costs and exact A6 to
   prove survival of the completed-input subtraction with an explicit epsilon
   budget. Then subtract early memory using the strict exponent margin.
3. Convert the physical window lower barrier and the matching upper bound into
   the full rate. Treat `Theta=0` with upper bound plus nonnegativity. Choose a
   fixed actual zero near the supremum, never an attaining zero.
4. Carry the uniform proof through unchanged MS1 schedules, normalize finite
   nonpositive prefixes only in a genuine horizon adapter, and derive the fixed
   continuous limit without restricting to integer horizons.
5. Only then review and promote exact original primary signatures, rerun their
   independent consumers and all source-pinned receipt/release gates. Root's
   current-source replay is separate and was still running when this report was
   prepared. This lane alone changes no original-root acceptance status.
