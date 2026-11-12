# The shape of the missing arithmetic

12 November 2026. Parent head `64a3dbd8e451b2d7eb94ceb394412abe8e2522e7`.
**Register and navigation document. RH and Step 4 remain OPEN.** Statements taken
from the 12 November Drive notes are DERIVED and not independently reviewed. The
Lean statements of contract M62 are compiled locally on the pinned toolchain and
need current-head CI. The exact certificates of `evidence/increment6b` are
recomputed in CI.

## Summary

So far, every route asks for one thing. It is a subexponential bound on a signed
pairing of the Möbius function with an explicit kernel; the same pairing can be
written with the prime discrepancy. The kernel is tame and changes sign. The
project's native objects reduce Step 4 to this pairing, but they do not weaken it.
In the fixed-field branch the pairing is the classical square-root cancellation
problem for the Mertens function, in smoothed form.

What is now known about the shape:

1. **How much may be lost** (compiled, M62). The missing inequality may compare
   an aperture with earlier ones and may lose polynomial or subexponential
   factors. It needs a delay bounded below. Positivity at intermediate apertures
   and contraction are not needed.
2. **What is paid** (DERIVED). The archimedean term is bounded polynomially, and
   so are the proper prime powers at the (PG)/(SE) level, the short Möbius part
   and the whole integer drive.
3. **What is not paid.** The signed Möbius/Mertens part.
4. **What a proof must use.** Explicit models or certified signs refute every
   supplier built only from positivity, PNT-level asymptotics, an Euler product
   with modified prime weights, low rank or a positive kernel. No model in the
   project preserves the identity `Λ = μ ∗ log`, with weight one on every integer,
   together with signed cancellation of `μ`.

## 1. The receiving side: what may be lost (compiled)

| Contract | Statement, one parity fixed | Lean |
|---|---|---|
| (SE), (PG), (C1), (SB) | slice floors at every positive rate, polynomially, cofinally | each equivalent to `RiemannHypothesis` (M60) |
| graded rates | all displacements `≤ a` iff fixed-rate floors at every rate above `a` | M60 |
| (DD) delay descent | `b(L) ≤ A(L) + G(L) · sup_{L₁ ≤ u ≤ L - h(L)} b(u)` at every large `L` | `riemannHypothesis_iff_delay_descent` (M62) |
| (ND) scale descent | `b(L) ≤ C(1+L)^d + C(1+L)^m · b(θL)`, `0 < θ < 1` | `riemannHypothesis_iff_scale_descent` (M62) |

Here `b(L)` is the negative part of the slice bottom. The contracts are stated
without a bottom function: a uniform bound `ε` on the earlier window gives the
bound `A + Gε` at `L`.

**Admissible costs** for (DD):

* the delay satisfies `h ≥ h₀ > 0` eventually;
* `A(L) ≤ e^{ηL}` eventually, for every `η > 0`;
* `2G(L) ≤ e^{η h(L)}` eventually, for every `η > 0`.

Every admissible cost profile that is eventually nonnegative gives a contract
equivalent to RH, because under RH every slice bound holds with error zero.

The six controls FrontierMutation36 to 41 mark the edges:

* the gain must be `e^{o(h)}`: with `2G ≤ e^h`, the function `b(L) = e^{L/2}` satisfies the premise (FM36);
* the delay must stay above a fixed `h₀ > 0`: with `h = 0` the premise compares `L` with itself and is vacuous (FM37);
* the conclusion is every positive rate, not a bounded floor: `b(L) = L` satisfies the premise (FM38);
* the scale form needs `θ < 1`: at `θ = 1` it holds for every source once `C ≥ 1` (FM39);
* the first apertures must be paid by an a priori bound; the compiled consumer uses the unconditional rate-one bound (FM40);
* under RH the contract follows only for nonnegative costs (FM41).

So the missing inequality may be lossy and relative. It may not be a
self-comparison, and its gain per step must be subexponential in the step.

## 2. Equivalent target forms (paper level)

Each form below is equivalent to RH through the consumer named. None is shown to
be easier than another.

| Form | Quantity | Consumer | Status |
|---|---|---|---|
| native slices | slice bottom in one parity | M60, M62 (compiled) | OPEN |
| scalar (S-SCALAR) | `E_e(L)`, energy of the even cutoff-3 unit vector; `T = w E_e` with `w = L / c_e²` polynomial | Laplace: an off-line zero `p` gives a simple pole with residue `2 m_p k_∞(p) ≠ 0` (signed-aperture note, section 4; DERIVED) | OPEN |
| fixed field | `S(T) = Σ_{n ≤ e^T} Λ(n) n^{-1/2} q4(T - log n)` | Laplace: `Ŝ(s) = -(ζ'/ζ)(s + 1/2) K(s)`, with `K = (L g)²` vanishing exactly to second order at `1/2` (log-delay note; DERIVED) | OPEN |
| Möbius return | `\|R_U(T)\| ≤ G · max_{t ≤ T - log(U+1)} \|S(t)\|`, in three versions listed below | delay lemma and fixed-field consumer (cutoff-scale note, Propositions A and B; DERIVED) | OPEN |
| Mertens | `\|M(x)\| ≤ C x^θ` gives fixed-field rate `θ - 1/2` through the bridge of section 3; `θ = 1/2 + ε` for every `ε` is RH | classical | OPEN |
| endpoint pairing | `J_P(L) ≤ C(1 + L)^d` (endpoint note, line 7.1) | scalar consumer | OPEN |
| long Möbius remainder | line 7.5 of the back-to-front audit | slice consumer | OPEN |

The three versions of the Möbius return are:

* `U = ⌊T²⌋` with `G = T^ε` for every `ε`;
* `U = ⌊e^{√T}⌋` with one fixed polynomial degree;
* `U = ⌊T^r⌋` with one degree common to all `r`.

The scalar `E_e` is not a vector of the quartic moment slice: its fourth moment
is `2880x ≠ 0`, checked exactly in `evidence/increment6b`. So the scalar route
needs its own formal adapter, while the whole-slice route reuses the compiled
(SE) consumer.

## 3. The split: what is paid and what is not

The exact bridge of the cutoff-scale note (DERIVED, by finite partial summation):

```
S(T) = ∫₀^T m(v) J(T - v) dv,      m(v) = e^{-v/2} M(e^v),      J = H' + H/2,
H(t) = Σ_{n ≤ e^t} (log n / √n) q4(t - log n).
```

| Part | Bound | Status |
|---|---|---|
| integer drive `H`, `H'` (weight one on every integer) | `\|H\| ≤ C_H (1+t)`, `\|H'\| ≤ C_H' (1+t)` with explicit rationals | DERIVED; the constants are recomputed exactly here |
| archimedean term | polynomial | DERIVED |
| proper prime powers | at most `L + L²/2 + 128`, so (PG) and (SE) may drop them; (SB) and (C1) may not | DERIVED |
| short Möbius part `F_U` | at most `2 C_H (1+T) √U` | DERIVED |
| **signed Möbius/Mertens part** | none | **OPEN** |

All of the difficulty sits in the last row: cancellation of `μ` against the
explicit, sign-changing kernel `J`. With the trivial bound `|M(x)| ≤ x`, the
bridge gives rate `1/2`, which is the unconditional rate of M60.

## 4. What any supplier must evade

| Control | Keeps | Breaks | Refutes |
|---|---|---|---|
| rank-one model `H_L = -e^{δL}` | low rank, norms | the source | source-blind low-rank or norm arguments for subexponential descent costs |
| positive comparison density | PNT asymptotics, positivity | the actual primes | PNT-only arguments: the positive and negative masses of the scale sum are each about `(C*/2) e^{L/2}`, with `C* = 328.70976` |
| Euler-exponent perturbation `a_p = 1 + ε cos(log p)/log p` | finite prefixes, prime support, positive Euler factors, a quantitative PNT | `Λ = μ ∗ log` with unit integer weights | arguments from the shape of the Euler product and the PNT; it does not refute arguments that use the bridge of section 3 |
| generalized integers (Diamond, Montgomery and Vorhauer) | very regular integer counting, multiplicative structure | weight exactly one on every integer | "the integers are well distributed" as the only arithmetic input |
| one off-line quadruple without a prime side (MP23) | explicit-formula shape, archimedean side | the Euler product | arguments from the archimedean side alone |

Certified signs and a cofinality fact refute further shortcuts:

* `J(4) > 0 > J(6)`, so no positive-kernel domination;
* `R` is negative at `N = 64` and positive at `N = 128`, so no all-time nonpositivity;
* `T(L) - T(L/2)` takes both signs, so no zero-loss monotone descent;
* two cofinal sets need not meet, so selected-predecessor arguments need the sets to coincide.

The Diamond–Montgomery–Vorhauer row is as summarized in Broucke, Debruyne and
Vindas, *Beurling integers with RH and large oscillation* (arXiv:2004.11501).

The perturbation constants `|A_{4,0}| = 2^19/5^9` and `|A_{5,1}| = 2^21/5^10` are
exactly `|G(1/2 + i)|²` in the large-aperture limit. The perturbation therefore
acts through a singularity at `s = 1 ± i`.

The sign changes of `T(L) - T(L/2)` at `L = 4, 8, 12` come from the first zero.
There `γ₁ L / 2π ≈ 9.00, 18.00, 27.00`, so the first zero's term nearly vanishes.

**Shape.** A supplier must use two things at once: the identity `Λ = μ ∗ log`
with weight one on every integer (the tame drive `H`), and signed cancellation of
`μ`. It must combine them in a way that none of these models preserves. That is
the classical difficulty. The native objects reformulate it without weakening it.

## 5. What would count as progress

* An independently proved arithmetic gain that gives one of the forms at a fixed
  rate below `1/2`. That is a zero-free half-plane, of quasi-RH strength.
* A proof of any form at every positive rate. That is RH.
* A theorem that one form fails for the actual field. That would narrow the
  shape further.

The external claims of half-planes (`7/8` and `0.8733819666133`) remain
unverified. One that passed a statement, axiom and dependency audit would give
rate `3/8` through `fixedRateMomentSliceBounds_of_re_le`, not closure.

## 6. Corrections to the round-7 consolidation

These corrections are made in [TARGET_CONSOLIDATION.md](../round7/TARGET_CONSOLIDATION.md)
and credited to the 12 November Drive reviews.

1. **Rates.** The squared energies of (E) and (F) grow at twice the rate of the
   field. The every-positive-rate equivalence of (U), (F) and (E) is unaffected,
   but fixed-rate correspondences must track the squaring. No quantitative
   equivalence of the full (E) and (F) contracts is established.
2. **What is ruled out.** Only the circular versions are ruled out: angle laws or
   ground-state convergence that assume the missing positivity. An independent
   proof of an RH-equivalent target is not circular.
3. **Where the predecessor is empty.** Under a dominant zero the empty predecessor
   holds at every late aperture. Without one, it holds only on a cofinal set,
   which is not shown to meet the production family.
4. **Size under RH.** Under RH, `E_e(L) = O(L^{-13})`, which is sharper than the
   recorded `12.94 / L⁵`.

## 7. Where things are

| Item | Location |
|---|---|
| M62 (delay and scale descent) | last section of `Zeta23/OPICARound4/ArithmeticFrontier/ZeroFreeFloor.lean` |
| controls FrontierMutation36 to 41 | `research/RHRC/integration/opica_round4/math_gate.py` |
| kernel certificates | [kernel_certificates.py](../kernel_certificates.py), [evidence/increment6b](../evidence/increment6b/SUMMARY.json) |
| Drive notes of 12 November | [SOURCE_LEDGER.json](../SOURCE_LEDGER.json), rows with an `increment6b` entry |
| open premises | [OPEN_PREMISES.json](../OPEN_PREMISES.json) |
