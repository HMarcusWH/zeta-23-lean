# FB-05 incompatibility program — same-state composition instead of one miracle lemma

> **Claim firewall: RH remains OPEN.**
>
> This document is a research-routing program. It records proved inputs, rigorous finite evidence, external research leads, candidate incompatibility pairs, and falsification tests. It does not promote any new theorem or claim.

## Core change in search strategy

The current search should not assume that FB-05 must be closed by one perfect arithmetic lemma.

The preferred target is now a **same-state incompatibility**:

```text
RH false
  -> exists one exact retained canonical state x
  -> A(x)
  -> B(x)

prove independently:
  A(x) -> C(x)
  B(x) -> not C(x)

therefore the exact RH-false state cannot exist.
```

The two component lemmas may each be much weaker than RH. What matters is that they are forced on the **same mathematical object**.

Permanent composition rule:

```text
same state
same aperture
same parity
same normalization
same production object
```

A statement about one witness and an incompatible-looking statement about a different witness proves nothing until a theorem identifies the objects strongly enough to compose them.

Informal mnemonic:

> RH false should not merely force the zeta arithmetic to perform one difficult trick. The useful contradiction may be that the same state must **fly through the air and swim underwater at the same time**.

## Existing project inputs that motivate this program

### PROVED — PR #27: the scalar prime-upper target is RH wearing a fake moustache

PR #27 theoremized

```text
arithmeticSideSubexponential_iff_criticalLine
```

so the R001 scalar target `ArithmeticSideSubexponential` is logically equivalent to the strip-zero form of RH.

Interpretation: proving that scalar prime-side upper bound directly is not a cheap auxiliary lemma. It is the terminal problem in different notation. This is OBS-008 and is a design warning against searching for another hidden RH-equivalent singleton target.

### PROVED — PR #28: off-line pairs have a negative-index signature unavailable to on-line positive atoms

At the division-free orthogonal witness, the exact off-line pair block has Hermitian value

```text
-c * gramDet(x,y)^2 < 0
```

under the stated positive-multiplicity/transversality hypotheses, while nonnegatively weighted sums of real rank-one/on-line blocks are PSD.

This is a genuinely different structural restriction. It does not close RH and does not by itself give the required windowed visibility, but it says an off-line pair cannot be synthesized by the on-line positive-atom geometry in that observable.

### PROVED — #153 through #163: several constraints already live on the same retained first-bad state

The current retained even-selected state simultaneously carries, where stated:

```text
negative canonical source-channel energy
R8(u_lambda) < 0
cross-parity secular/source identity
odd-bad OR explicit-source-moment-nonzero fork
h^(7)(0) = -2*(2*pi)^6*M4(u_lambda)
exact finite-prime sampling of the same quadratic-normal source observable
exact R8-R9 boundary identity through |h^(7)(0)|^2
```

This is why an incompatibility strategy is now realistic: much of the difficult object-identification work has already been done.

### EXPERIMENTAL SIGNAL — PR #180: local derivative orientation is visible at exact frozen centers

For the frozen Q14 primary exact centers:

```text
POINT_DERIVATIVE_BASIN_BRACKETED
MINIMUM_ORIENTED
left centers:  3/3 Delta_2' < 0
right centers: 3/3 Delta_2' > 0
```

The nonzero-width Schur boxes are not yet a sign result; they are `SCHUR_OUT_OF_H1_SCOPE`. The immediate finite task remains centered H1 recovery, followed by a Schur-box retry and only then second-order centered propagation if needed.

## External research inputs worth composing carefully

These are research leads, not project theorem authority.

### Lamzouri — arXiv:2609.02882v2

Unconditionally, more than 67.25% of nontrivial zeta zeros are simple and on the critical line, with additional distinctness/rigidity bounds.

Important non-independence warning: Lamzouri explicitly explains that his Hilbert-space proof and the Alpöge–Furman/Claude finite-matrix proof are different realizations of essentially the same quadratic second-moment / Montgomery–Taylor extremal structure. Do **not** count them as two independent 67.25% constraints and add their percentages.

### Wang — arXiv:2609.07918v1

Extends the Lamzouri mechanism to short intervals `(T, T+T^theta]`, with explicit lower bounds for simple critical-line zeros. This is potentially more useful for FB-05 than the global percentage because it localizes the forced critical-line population.

### Groskin — arXiv:2607.02828v3

Provides an exact finite Guinand–Weil dictionary for its Galerkin family:

```text
<v,Q_infty v> = sum_over_zeta_zeros g_v(z)
```

with an exact finite source quotient and a separate archimedean tail-order theorem. This is a candidate bridge between finite arithmetic quadratic forms and explicit zero-side sampling, but its exact normalization/object must be matched to the project production state before composition.

### Shi — arXiv:2609.04908v1

Constructs finite Prime–Weil matrices / contrast pencils and records the different spectral behavior of real ordinates versus hypothetical off-line conjugate pairs. Its own stated remaining problem is a relative prime-to-zero perturbation/transfer theorem. Use this as structural guidance, not as a solved transfer theorem.

## Why the new zero-density results do not prove RH by counting

The 67.25% theorem is fully compatible with an asymptotically sparse exceptional set of off-line zeros. One off-line quartet among an enormous number of critical-line zeros easily fits inside the remaining proportion.

Therefore this route must **not** be phrased as

```text
67.25% + 67.25% > 100%
```

or any variant of percentage addition.

The useful target is instead a same-window / same-test / same-state domination statement:

```text
positive contribution forced by sufficiently many nearby simple critical zeros
    >
maximum negative contribution available to the exceptional/off-line sector
```

for the special band-limited/canonical witness forced by the first-bad construction.

That kind of theorem could be much narrower than full Weil positivity and therefore need not be RH-equivalent by construction.

## Candidate incompatibility pairs

### Pair A — contact orientation clash

**Side 1: first-bad/contact geometry.** A hypothetical first bad contact imposes a definite crossing/orientation requirement on the local determinant/Schur scalar.

**Side 2: canonical arithmetic derivative law.** Existing fixed-cell infrastructure preserves

```text
A(L) = -log(L) I + R(L).
```

If the production Schur-envelope derivative can be theoremized, the candidate decomposition is

```text
P'(L) = Re <u_L,A'(L)u_L>
      = -||u_L||^2/L + Re <u_L,R'(L)u_L>.
```

A contact-local bound on the arithmetic remainder drift could force the opposite orientation.

At H1 contact,

```text
Delta_2 = aP
P = 0  ->  Delta_2' = aP'
a > 0
```

so a contact-local `P'` sign law transfers to the determinant without requiring global Schur monotonicity.

**Status:** LEAD / HYPOTHESIS. The production envelope derivative and remainder domination are not yet proved.

### Pair B — negative-index separation versus critical-line sampling rigidity

**Side 1:** PR #28 says a visible off-line pair forces a genuinely negative/transverse Gram direction that no nonnegative on-line rank-one combination reproduces.

**Side 2:** Lamzouri/Wang-style critical-line population plus pair-correlation information may force a lower sampling/frame bound for the **same band-limited witness**.

Schematic target:

```text
sum_{simple critical gamma in I} |F_u(gamma)|^2 >= C_I * ||F_u||^2
```

strong enough that the exact zero-side quadratic value cannot be negative.

**Bridge debt:** show that the canonical retained witness maps into the required test family with exact enough normalization, and quantify exceptional/off-line contributions. Counting alone is insufficient.

### Pair C — local first-bad event versus short-interval zero rigidity

A retained q13/Q14 first-bad state requires a very specific local negative/contact event. Wang's short-interval theorem forces a controlled population of simple critical zeros in power-length windows at high ordinates.

The question is not whether many critical zeros exist. It is whether their forced local distribution makes the **specific first-bad test function** too positive to realize the retained negative event.

**Status:** LEAD. Requires a localization theorem matching the first-bad test support/window to the short-interval zero theorem.

### Pair D — two-parity squeeze

#161 already puts the selected parity and opposite parity into one fork:

```text
odd successor bad OR explicit source moment != 0
```

A useful contradiction may come from proving two modest parity restrictions that close the two escape hatches separately on the same retained state, rather than one theorem that proves universal successor positivity.

**Status:** OPEN / composition target.

### Pair E — growth detector versus finite-energy/sampling control

R001 supplies target-adaptive exponential visibility of an off-line zero after pole killing, while the finite explicit-formula/Weil side supplies exact quadratic identities for restricted test families.

Potential route: force one and the same adapted witness to satisfy both a growth lower bound from the off-line pole and an independently derived upper/energy bound from localized arithmetic/zero sampling.

**Warning:** the naive scalar upper bound is exactly OBS-008 and is RH-equivalent. Any revived version must genuinely use a narrower observable, local window, extra structure, or same-state coupling rather than restating `ArithmeticSideSubexponential`.

## Incompatibility matrix to maintain

For every candidate pair, record four columns:

```text
1. property forced by RH-false / first-bad state
2. independently provable opposing property
3. theorem needed to identify them on the same object
4. fastest falsification test
```

Initial matrix:

| Pair | RH-false / first-bad property | Opposing property sought | Missing bridge | Fastest falsifier |
|---|---|---|---|---|
| A | first-contact crossing orientation | canonical log-drift/remainder forces opposite contact orientation | production Schur-envelope derivative | split the two derivative pieces at #180 frozen centers |
| B | negative transverse Gram direction | same witness gets positive lower frame/sampling energy from simple critical zeros | canonical witness -> exact band-limited zero-side family | finite zero-side replay with controlled exceptional contribution |
| C | local q13/Q14 bad/contact event | short-window critical zeros force enough local positivity | aperture/window correspondence | compare support scale with Wang window regime |
| D | selected parity badness/source fork | opposite parity restriction closes remaining branch | same-state parity composition | same-q/N opposite-parity executable controls |
| E | target-adaptive off-line growth | local/structured arithmetic energy upper bound | non-RH-equivalent observable restriction | test whether proposed upper bound collapses to OBS-008 |

## Falsification firewall

Before investing in a candidate incompatibility, try to kill it.

- **Sparse-exception test:** does the proposed use of 67.25% fail immediately if the off-line zeros have density zero? If yes, counting alone is useless.
- **Independence test:** are two allegedly independent constraints really the same second-moment inequality in different language? Lamzouri versus the finite-matrix 67.25% proof is the model warning.
- **Same-object test:** do both properties apply to the exact same retained vector/state/aperture/parity/normalization? If not, the composition is invalid.
- **Normalization test:** do not identify Groskin/Shi/other external finite matrices with the project canonical source without an exact bridge theorem.
- **Exceptional-budget test:** can a small number of off-line zeros contribute arbitrarily large negative mass to the chosen test? If yes, density information alone cannot dominate them.
- **Mustache test:** does the allegedly modest opposing lemma become RH-equivalent after unpacking definitions, as happened in PR #27? If yes, reject it as a cheap intermediate target.
- **Global-monotonicity test:** do not revive DR-022. A contact-local derivative restriction is acceptable; a global fixed-sign Schur derivative requires new evidence.
- **Circularity test:** neither side of the contradiction may smuggle successor positivity/negative-root exclusion into its assumptions.

## Immediate execution order

The local finite microscope and the incompatibility program should run in parallel.

### Track 1 — local Q14 microscope

```text
centered H1 recovery
-> retry Schur derivative boxes
-> if needed, centered Delta_2'' propagation
-> signed neighborhoods
-> stationary isolation
-> sign of Delta_2 at isolated stationary state
```

This determines what local arithmetic behavior actually needs explanation.

### Track 2 — composition search

```text
build/maintain incompatibility matrix
-> theoremize the cheapest same-state bridges
-> test candidate opposing properties on the already-retained state
-> kill pairs that collapse to RH-equivalent or density-only statements
-> promote only a pair whose two sides survive adversarial testing
```

Highest-leverage theorem target currently visible:

```text
same-state contact geometry
+
production Schur-envelope/log-drift arithmetic restriction
-> incompatible contact orientations
```

Highest-leverage external-composition experiment currently visible:

```text
off-line negative-index witness
+
localized simple-critical sampling/frame lower bound
-> can the same exact zero-side quadratic value remain negative?
```

## Success criterion for FB-05 under this program

FB-05 does **not** require discovering a standalone theorem equivalent to

```text
all canonical successors are nonnegative.
```

It is enough to obtain two independently meaningful theorem-backed properties of the exact forced state whose conjunction is impossible.

Desired final shape:

```text
PROVED: RH-false retained state -> A
PROVED: RH-false retained state -> B
PROVED: A -> C
PROVED: B -> not C
--------------------------------
DERIVED: no retained RH-false state
```

Only after the exact composition is formalized and validated may the route advance to FB-06 negative-root exclusion and the terminal RH seam.

## Claim firewall

```text
PROVED: PR #27 R001 scalar target is RH-equivalent
PROVED: PR #28 block-level negative-index separation under its hypotheses
PROVED: same-state retained source/Riesz/mixed-jet package through PR #163
EXPERIMENTAL SIGNAL: PR #180 exact-center minimum-oriented derivative basin
EXTERNAL THEOREM: unconditional >67.25% simple critical zeros (Lamzouri / Alpoge-Furman lineage)
EXTERNAL THEOREM: short-interval simple-critical lower bounds (Wang)
EXTERNAL THEOREM: exact finite dictionary in Groskin's stated Galerkin family
LEAD: compose these into a same-state incompatibility
OPEN: finite-width q13/Q14 derivative sign neighborhoods
OPEN: contact-local arithmetic derivative law
OPEN: sampling/frame domination for the canonical retained witness
OPEN: simultaneous-parity exclusion
OPEN: FB-05
OPEN: negative-root exclusion
OPEN: RH
```

**RH remains OPEN.**
