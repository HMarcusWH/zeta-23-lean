# W2-ZS post-green research settlement — F0-B frontier

Status: **POST-GREEN RESEARCH SETTLEMENT / RH OPEN**

This document records the research consequences of merged PR #83 and the authority cleanup through PR #84. It is historical research state, not theorem authority. Live Lean/compiler/CI, the machine registries and the active R003 README remain authoritative.

## Exact validated state

~~~text
repository = HMarcusWH/zeta-23-lean
main = 9e899ca322116e28a56a4412d48aef0052b86fbe
tree = ad636143768dcaa4dbeb23a0ea295d7b2d6b1c9b
merged through = PR #84

PR #83 theorem head = 556be6c2b42e912c58751988c580ab4e0091822d
PR #83 merge = 7b8e0cc9abbaeff97d88ec67ada40734619a8d07

PR #84 final validated head = 1a518c9ebd408fa559c5eff281eafe5ff3b2af48
PR #84 merge / current main = 9e899ca322116e28a56a4412d48aef0052b86fbe

date = 2026-09-01
RH = OPEN
~~~

PR #83 exact theorem head passed both repository workflows. PR #84 exact cleanup head also passed both repository workflows before merge.

Headline #83 axiom surface:

~~~text
[propext, Classical.choice, Quot.sound]
~~~

## What became formally true

### PROVED — concrete-zeta one-sub symmetry package

PR #83 theoremizes the actual concrete-zeta carrier symmetry needed for the zero-side route:

~~~text
zeta_conj_zero
zeta_one_sub_zero
zeta_mult_one_sub

zetaOneSubEquiv
zetaOneSubEquiv_mult

gammaOf_one_sub
gammaOf_zetaOneSubEquiv
~~~

The carrier map is the actual involution

~~~text
rho -> 1-rho
~~~

with multiplicity preserved, and

~~~text
gammaOf(1-rho) = -gammaOf(rho).
~~~

### PROVED — Fourier reflection and legal zero-sum reindex

PR #83 proves the exact paper Fourier convention under physical reflection and reindexes the concrete zero sum through a genuine carrier equivalence.

The critical legality property is explicit: reindexing/addition/scalar contraction is performed only after the relevant Summable certificates are available.

Key declarations include:

~~~text
paperFT_zeroSideReflectTest
zetaLiteratureZeroTsum_reflect_eq
zeta_literatureRHS_halfEven_eq
~~~

### PROVED — direct diagonal W/localized-additive identity

For every compact C² complex-valued test h:

~~~text
zetaZeroConfig.W h h
  = Zeta23.CCM.localizedWeilAdditiveRHS h h.
~~~

Production theorem:

~~~text
Zeta23.ExceptionalZero.zeta_W_self_eq_localizedWeilAdditiveRHS
~~~

Registered claim:

~~~text
R003_WEIL_LOCALIZED_ADDITIVE_SELF_BRIDGE
~~~

No aperture, pole-neutrality, mu/gamma-evenness or weighted gamma-integrability hypothesis is needed.

### PROVED — strict-aperture negative localized-additive witness

Composing W1 with the generic diagonal bridge gives, for every concrete off-line zero:

~~~text
exists L>0, r>0, h,
  L = 4*r
  and ContDiff R 2 h
  and HasCompactSupport h
  and tsupport h ⊆ Ioo r (3*r)
  and tsupport h ⊆ Ioo 0 L
  and paperFT h ( I/2) = 0
  and paperFT h (-I/2) = 0
  and Re(localizedWeilAdditiveRHS h h) < 0.
~~~

Production theorem:

~~~text
Zeta23.ExceptionalZero.
exists_strictAperture_poleNeutral_negativeLocalizedWeilAdditiveRHS_of_offLine_zero
~~~

Registered claim:

~~~text
R003_STRICT_APERTURE_NEGATIVE_LOCALIZED_ADDITIVE_WITNESS
~~~

Companion minimal wrappers expose the exact F0-B/F1-roadmap input.

## What changed

The primary internal dependency graph compressed.

Before #83, the shortest planned internal route required a possible explicit analytic reflection package:

~~~text
I0 pole neutrality
I1 mu/gamma reflection
I2 weighted gamma-channel integrability
-> W2-B
-> W2-C
-> F0-B.
~~~

After #83:

~~~text
W2-A [PROVED]
-> concrete zero-side evenization [PROVED]
-> direct diagonal W2-C endpoint [PROVED]
-> F0-B [OPEN].
~~~

The old analytic W2-B route is not false. It is simply no longer required on the shortest path.

**Classification:** OPEN / DORMANT INDEPENDENT CROSS-CHECK.

Do not relabel it PROVED merely because its intended endpoint is now proved by a different route.

## Upstream implications

### Concrete zeta was the right abstraction level

The successful proof uses Schwarz conjugation in addition to the existing functional-equation symmetry.

No stronger field was added to generic ZeroConfig.

That is evidence that the reusable abstraction boundary is currently:

~~~text
generic ZeroConfig:
  existing reflection structure

concrete zeta:
  extra Schwarz symmetry
  -> one-sub zero-side equivalence.
~~~

Do not generalize ZeroConfig unless another theorem needs the same stronger interface.

### The gamma/digamma channel is no longer primary infrastructure

The proof never opens the pole/prime/gamma decomposition of literatureRHS.

Therefore mu-evenness and weighted gamma-integrability should not be built merely because they appeared in an older execution plan.

They remain useful only for:

- independent analytic cross-validation;
- future theorems that need the decomposed channel itself.

### Regularity upgrade is conditional

The current canonical detector seed interface exports C⁴ and the current pole-killer theorem consumes two derivatives:

~~~text
contDiff_poleKilled : C⁴ -> C².
~~~

If F0-B later requires a C⁴ final pole-killed witness, the natural upstream target is therefore at least C⁶ seed regularity.

This is a **LEAD / HYPOTHESIS**, not theorem state.

Do not build a gratuitous C∞ layer.

## Downstream implications

The shortest internal route is now:

~~~text
off-line zero
  -> strict negative localized-additive witness    [PROVED]
  -> F0-B finite approximation/continuity          [OPEN]
  -> G1-A finite restriction                       [PROVED]
  -> F1 canonical finite negative obstruction      [OPEN].
~~~

Thus F0-B is the primary internal mathematical frontier.

### F0-B1 — boundary-flat global C² finite approximation

For a centered trigonometric polynomial

~~~text
p(x) = sum_n u_n exp(2*pi*i*n*x/L),
~~~

forcing endpoint jets of order 0,1,2 to vanish gives coefficient constraints

~~~text
sum u_n = 0
sum n*u_n = 0
sum n^2*u_n = 0.
~~~

A candidate construction is:

~~~text
raw Fourier approximant
+ fixed three-mode reserve correction
-> exact endpoint jets zero
-> global compact C² zero extension.
~~~

If this construction is legal, #83 applies to every approximant:

~~~text
localizedWeilAdditiveRHS(p_N,p_N)
  = W(p_N,p_N).
~~~

Then it suffices to prove

~~~text
W(p_N,p_N) -> W(h,h) < 0.
~~~

### F0-B2 — direct localized-additive continuity

The existing G0/G1-A finite vectors are already legal for the finite additive restriction theorem even though arbitrary zero extensions are not globally C².

An alternate route is therefore:

~~~text
v_N -> h in a suitable topology
and
localizedWeilAdditiveRHS(v_N,v_N)
  -> localizedWeilAdditiveRHS(h,h) < 0
~~~

without first making every v_N a global C² test.

The route should be chosen by theorem size and falsification results, not aesthetic preference.

### Load-bearing continuity question

The central analytic issue is family-level control.

**Critical firewall:**

~~~text
for every N:
  Summable(Wsummand(p_N,p_N))

does NOT imply

exists one summable majorant controlling all N.
~~~

Any zero-side dominated-convergence argument must prove uniform domination or replace it with another quantitative continuity theorem.

## Resurrected routes

### Boundary-flat Fourier approximation

**Status:** ACTIVE CANDIDATE / BOUNDED F0-B SPIKE.

This route becomes more attractive after #83 because legal compact C² finite approximants automatically share the exact W/localized-additive identity with the target.

The earlier endpoint-jet algebra is therefore worth revisiting.

### Direct additive continuity

**Status:** ACTIVE CANDIDATE / BOUNDED F0-B SPIKE.

This route remains competitive because it may bypass global C² zero extension entirely.

### Old analytic W2-B

**Status:** DORMANT INDEPENDENT CROSS-CHECK.

The failure reason was not mathematical impossibility. The route was superseded by a smaller proof surface.

Reactivate only for independent validation or when explicit channel decomposition becomes useful.

### Source-faithful lane

**Status:** ACTIVE PARALLEL / CROSS-CHECK.

The #84 split remains authoritative:

~~~text
S-GEOM / S-IFACE
  -> G1-B1B / G1-final

separate:
S-NEG or exact W/localized/QW sign composition

then:
G23 -> F1.
~~~

OBS-015 remains load-bearing.

## New RH-relevant clues

### LEAD — one exact identity may control both target and approximants

#83 gives the same exact diagonal identity for every legal compact C² approximant and for the target witness.

If F0-B1 closes, the finite approximation problem can potentially be phrased entirely as:

~~~text
approximate in a W-controlling topology
while staying in the boundary-flat finite sector.
~~~

That is structurally cleaner than separately analyzing the pole/prime/gamma channels on every approximant.

### LEAD — strict collar may make endpoint correction cheap

W1 gives the derived collar

~~~text
tsupport h ⊂ (L/4,3L/4).
~~~

Hence the target vanishes on fixed neighborhoods of both endpoints.

This makes periodicization and endpoint-jet correction unusually favorable compared with a generic compactly supported test touching the boundary.

### LEAD — attack the obstruction space, not RH directly

F0-B can be viewed as ruling out a class of possible counterexamples to finite detectability:

> a strict negative localized-additive witness that cannot be captured by any finite centered sector.

A theorem showing such witnesses are always finitely detectable would be exactly F1 after G1-A.

## Falsification checks

Run these before a monolithic F0-B implementation.

### F0B-L1 — legal zero extension

Prove or falsify:

~~~text
endpoint jets 0,1,2 vanish
  ->
zero extension of the finite trigonometric polynomial
is ContDiff R 2.
~~~

If the existing representation makes this theorem unnecessarily difficult, reconsider the representation early.

### F0B-L2 — reserve-mode correction

Choose a fixed three-mode block and theoremize the endpoint-jet correction system.

Required facts:

- correction matrix invertible for L>0;
- correction solves all three endpoint conditions exactly;
- correction coefficients tend to zero when endpoint residuals tend to zero.

### F0B-L3 — family-level W continuity

Prove or falsify a quantitative theorem sufficient for

~~~text
W(p_N,p_N) -> W(h,h).
~~~

Fast candidate: fixed common support + uniform C² control -> summable zero-side majorant.

If that fails, do not pretend individual Summable certificates suffice.

### F0B-L4 — direct additive continuity

In parallel test whether the existing finite vectors admit a smaller direct estimate for

~~~text
localizedWeilAdditiveRHS(v_N,v_N)
  -> localizedWeilAdditiveRHS(h,h).
~~~

### Regularity test

Only if raw Fourier convergence requires it, theoremize the minimum higher-order seed regularity. Current derivative accounting suggests C⁶ seed for a C⁴ final pole-killed witness.

## Highest-leverage next moves

1. Prove/falsify F0B-L1 on the existing finite-vector representation.
2. Theoremize the 3x3 reserve-mode correction and coefficient decay.
3. In parallel probe the smallest family-level W-continuity estimate.
4. Compare against direct localized-additive continuity before committing to a large analytic library.
5. Select F0-B1 or F0-B2 only after the bounded spike.
6. Compose any successful strict-negative finite transfer immediately with G1-A.
7. If that yields F1, stop and perform a full post-green research pass before K0-K3.
8. Keep the source lane active as independent validation, not as a hidden prerequisite for the internal route.

## Standing questions

### Given everything now formally true, what becomes possible that was not possible before?

A hypothetical off-line zero now produces a strict negative value of the *same localized additive functional already theorem-locked on every finite centered sector by G1-A*. The missing link is approximation/continuity, not identification of the functional.

### If this contains a clue toward RH, where does it propagate?

~~~text
off-line zero
  -> negative localized additive witness
  -> finite detectability F0-B
  -> canonical finite negative obstruction F1
  -> K0-K3 finite-wall program.
~~~

### What experiment, lemma or reformulation most efficiently tells us whether the clue is real?

The smallest high-information test is whether boundary-flat finite approximants can be made globally C² with vanishing correction while obtaining a genuine family-level W continuity theorem. In parallel, test whether direct localized-additive continuity is smaller.

RH remains **OPEN**.
