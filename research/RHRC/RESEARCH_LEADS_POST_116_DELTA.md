# RHRC research leads delta — post PR #116

> **Claim firewall: RH remains OPEN.**
>
> This file records the post-green research implications of merged PR #116. It is a research-control delta, not a theorem registry. Mathematical authority remains the exact Lean/compiler/CI surface. PR #116 adds no new Lean theorem and does not advance the theorem-state anchor beyond PR #115.

## Exact authority split

~~~text
live main after #116 = 8921572170e89d74216f0c5577b669696626219e
live main tree = fc138b517c6835230515167386eafe3ef3495baf

theorem-state anchor = PR #115 merge a2fecffbef8fed1fdfba373aa5756acf2618e2a1
theorem tree = 47a2601e3464b0b4248e61c52b4560681f73c986
E1 cubic-shell incidence = PROVED / MERGED

control-plane anchor = PR #116 merge 8921572170e89d74216f0c5577b669696626219e
validated PR head = b5e09880b2996e41364b3abbcc35710399a0f262
validated synthetic merge = a4d37c0fa0ce5a1e44e321924292a2b3a7920146
validated tree = fc138b517c6835230515167386eafe3ef3495baf
RHRC #776 = SUCCESS
Permansson #549 = SUCCESS
RH = OPEN
~~~

The validated PR merge tree and merged-main tree are identical. #116 changed research-control, assurance, archaeology and documentation infrastructure; it did not change `Zeta23/**/*.lean`, claim authority, route authority or the terminal RH status.

---

## L-116-01 — canonical cubic coordinates for deformation diagnostics

**Research status:** READY  
**Formal status:** DERIVED / OPEN FORMALIZATION

PR #115 proves, for either parity in the stated nontrivial range,

~~~text
c_N := intrinsicCubicShellPart p N != 0
c_N ∈ intrinsicParitySuccShell p N
dim_C intrinsicParitySuccShell p N = 1
~~~

This removes the need to choose an arbitrary shell basis for the deformation-budget quantities. A scale-free canonical definition is

~~~text
q_N = Re <T c_N, c_N> / <c_N,c_N>
beta_N^2 = ||B c_N||^2 / <c_N,c_N>
~~~

with the denominator nonzero because `c_N != 0`.

**Why this matters:** E2, E3 and the deformation-budget lane can share one theorem-backed shell coordinate instead of introducing a separate normalization convention.

**Falsification / firewall:** nonzero shell coordinate does not mean `c_N` is pure shell in the ambient successor carrier, and shell invariance is still not proved.

---

## L-116-02 — E2 + E3 should theoremize the one-step deformation bound

**Research status:** ACTIVE COMPOSITION  
**Formal status:** LEAD / HYPOTHESIS

The current diagnostic inequality is not an independent route from E2/E3. The expected theorem chain is

~~~text
#115 canonical cubic shell incidence
  -> E2 cubic-normalized shifted Schur
  -> E3 projected symmetry / shifted coercivity / resolvent estimate
  -> certified one-step deformation inequality
~~~

Writing

~~~text
g_N = q_N - mu_N
d_N = mu_N - lam
~~~

one expects the normalized Schur identity plus a predecessor resolvent bound to yield

~~~text
g_N + d_N <= beta_N^2 / d_N

d_N (g_N + d_N) <= beta_N^2
~~~

and therefore

~~~text
d_N <= (sqrt(g_N^2 + 4 beta_N^2) - g_N)/2
~~~

and, when `g_N > 0`,

~~~text
d_N <= beta_N^2 / g_N.
~~~

The square-root expression remains diagnostic until the operator hypotheses are theoremized. The safe route is the E3 coercive resolvent estimate.

---

## L-116-03 — rigidity horizon plus badness persistence can eliminate the whole N-axis

**Research status:** ACTIVE HIGH-VALUE LEAD  
**Formal status:** DERIVED STRATEGY / OPEN CERTIFICATION

Exact N-flow already proves upward persistence of parity badness at fixed `L` and parity. Therefore a genuine positive rigidity horizon is stronger than a finite-window contraction.

If, for fixed `(L,p)`, one certifies

~~~text
H_Nstar = mu_lower_Nstar - R_upper_Nstar > 0
~~~

with `R_upper_Nstar` bounding the complete future deformation tail, then:

1. no earlier size could have been bad, because badness would persist upward to `Nstar` and contradict the positive floor there;
2. no later size can become bad, because the complete remaining deformation budget is insufficient to consume the positive headroom.

Hence a fully certified horizon would exclude every `N` for that fixed `(L,p)`.

**Important correction:** this does not require one universal horizon independent of `L`. The logically necessary target is all-`L` certification, potentially with `Nstar=Nstar(L,p)`. Uniformity in `L` is stronger than required unless a later theorem specifically needs it.

---

## L-116-04 — shell projection turns the cubic defect functional into the new quotient coordinate

**Research status:** READY / CHEAP FORMALIZATION CANDIDATE  
**Formal status:** DERIVED / OPEN FORMALIZATION

PR #112 proves the exact factorization

~~~text
F_N(z) = ell_N(z) • g_N
~~~

and PR #115 proves that the canonical cubic generator has nonzero intrinsic shell coordinate. Applying the canonical shell projection should therefore give

~~~text
shellPart (F_N z) = ell_N(z) • shellPart(g_N)
~~~

with `shellPart(g_N) != 0`, so one expects

~~~text
shellPart(F_N z) = 0  <->  ell_N(z) = 0.
~~~

This reframes the old abstract question `ell_N != 0` geometrically: is the exact parity defect inherited from the predecessor, or does it enter the unique new one-step quotient direction?

**Firewall:** exact factorization plus nonzero generator still does not prove `ell_N` is nonzero for any specific argument or that the defect operator has exact rank one.

---

## L-116-05 — deformation-budget first-break hierarchy

**Research status:** TESTING  
**Formal status:** EXPERIMENTAL / DIAGNOSTIC

The cheap bounded test should measure, for both parities and several fixed positive `L` values,

~~~text
g_N = q_N - mu_N
beta_N
beta_N^2 / g_N
~~~

in that order.

Kill conditions:

1. `g_N` fails to stay usefully positive;
2. `beta_N` does not exhibit useful decay;
3. `beta_N^2/g_N` is not plausibly summable;
4. behavior degenerates across the required `L` range;
5. reduced/reference decision commutation fails.

Decay of `beta_N` alone is not enough. For example, `beta_N ~ N^(-1/2)` with a bounded positive gap gives `beta_N^2 ~ 1/N`, which still has a divergent tail.

No fitted tail, finite prefix or local residual is a horizon certificate.

---

## L-116-06 — retro archaeology is high-recall but currently needs precision control

**Research status:** CONTROL HARDENING  
**Formal status:** CONTROL-PLANE ONLY

The first real-history Control-v2 run recovered 226085 deformation-budget archaeology hits, of which 226047 came from the generic alias `fold`. This proves the exhaustive mechanism works, but it also proves that generic vocabulary can swamp the relevant clue set.

The hardening rule is:

~~~text
complete search != relevant search
~~~

Use precise concept aliases for admission-critical archaeology. Generic terms such as `fold`, `rupture` and `slack` must not operate as unconditional standalone aliases.

Also state scope exactly: archaeology searches all historical Git refs within the declared search paths, not every byte in the repository unless those paths are explicitly widened.

---

## Resurrected route family

Older `evolving canvas`, `residual headroom`, `detectability budget` and related ideas are worth reconsidering because the prerequisite state has changed materially:

~~~text
exact centered N-flow
+ one-dimensional intrinsic shell
+ shifted Schur reduction
+ exact cubic factorization
+ theorem-backed cubic-shell incidence
~~~

This is not a revival of DR-010. The fitted-small-commutator -> eigenvector-convergence shortcut remains dead for the same spectral-gap reason. The current route uses exact nesting and exact block geometry.

---

## Current execution order after #116

~~~text
THEOREM LANE
  E1b/E2 canonical cubic shell scalar multiple + scale-free Schur
    -> E3 projected symmetry / coercivity / resolvent
    -> certified one-step deformation theorem if the paper test survives
    -> E4 parity nullity / resonance as an additional rigidity lane

DIAGNOSTIC LANE
  probe g_N, beta_N, beta_N^2/g_N
    -> attempt a certified summable tail only if the first breaks survive

CONTROL LANE
  require typed interval coverage, horizon evidence, decision commutation where applicable,
  precise archaeology scope and fail-closed PRUNE semantics

SOURCE LANE
  G1-B1B -> G1-final -> S-NEG -> G23

RH OPEN
~~~

**RH remains OPEN.**
