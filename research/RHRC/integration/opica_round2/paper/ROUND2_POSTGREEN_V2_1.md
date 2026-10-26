# OPICA Round 2 — post-green research and revised specification, v2.1

**Marcus Hermansson · Riemann Hypothesis research · 25 October 2026**  
**Disposition: Step 4 OPEN; RH OPEN.**  
**New Lean declarations compiled in this investigation: 0.**

## 1. Outcome


**Completeness revision 2.1.** A second pass found substantive omissions in v2.
Sections 2 and 10 now reflect the new source pin and expanded specification;
Section 15 contains the full omission audit, precise restored statements,
deferred-lane register and carry-forward decisions. The original v2 remains
in the package for comparison. The four additions are **S14 CT1 scalar limits,
S15 finite neutral approximation, S16 fixed-filter global sufficiency, and
S17 phase-complete positive observations**. None supplies the missing terminal
estimate. [C1–C8]

The investigation did not establish a global Step 4 closure. The completed
OPICA mathematics makes the remaining obligations much more precise, but none
of the independently checked workflow outputs supplies the required opposing
arithmetic estimate, causal approximation theorem, or outgoing-contact sign.

This document is the requested fallback: **a revised, source-pinned OPICA Round
2 handoff**, incorporating the three attached October 25 documents, the earlier
October 25 harvest and closure investigation, the current PR, and the current
Drive route dossiers. It preserves the original 25 proposed contracts and adds
17 explicitly proposed supporting amendments, including four restored by the completeness audit. The optional C2/C3/C4 programme, historical control registry, 49-requirement/WP carry-forward and complete module map are now explicit. Those numbers describe work
records, not new theorems or mathematical novelty. The four terminal research
targets remain separately OPEN.

The most useful changes to the preliminary Round 2 plan are concrete:

1. Retain the fixed-source causal probe, but do not begin with a small raw Gram
   optimization: the actual source gives a rigorous finite-size obstruction.
2. Make the **fixed, source-preserving filtered primal certificate** the first
   executable/formalization milestone. Its rational four-column baseline has
   been independently reconstructed here with exact arithmetic.
3. Carry the original source and transported dual witness through every filter.
   A small filtered norm without its corresponding witness margin proves nothing.
4. Add quantitative prefix constraints and adaptive error budgets. Successful
   coefficients must approach the actual Möbius coefficients at every fixed
   index, and input norms cannot remain bounded for the new undamped target.
5. Keep A, C, and D as genuine alternative analytic research routes. They are
   not discharged by formalizing the causal certificate infrastructure.
6. Preserve and strengthen the adversarial controls. A fresh paper deduction
   in this pass gives an ordered negative minor in the **literal native
   prime-plus-Archimedean jump gain**, excluding one tempting total-positivity
   shortcut without modifying the prime coefficients.

No repository source was edited, no PR was merged or posted to, and no existing
research contract was silently rewritten. The originals are included unchanged
in the companion package.

## 2. Exact evidence and coverage

### 2.1 Repository pin and authority

| Object | Verified identity or scope |
|---|---|
| PR | [HMarcusWH/zeta-23-lean #294](https://github.com/HMarcusWH/zeta-23-lean/pull/294), open draft at the inspected snapshot |
| Current inspected head | `416aec21d4d6634675639b5397cc300d1f826e34` |
| Current tree | `0506bca8ffe613e9cd9ab844650a1141d4494f66` |
| Accepted parent/base | `d53dd70d38b0762af130b1d19b795af259f505f5` |
| Delivered-v2 source | `f5bafbc575c5663cdfaa4ce9e1de69d9fb9f9486`, tree `fe6dd1dc24b590209bab629d9424348722aadd56` |
| Change from delivered v2 | Two workflow setup lines and eight generated metadata files; **no Lean or dependency-pin changes** |
| Native compiler/dependencies | Lean `4.33.0-rc2`; Mathlib `51e6992efd06126df61a496bebf8f49482a4e129` |
| Current workflow snapshot | **25 October 2026, 17:07:17 UTC / 18:07:17 Europe/Stockholm (CET)** |

At that dated snapshot, 22 current-head runs had 76 declared jobs: 51 successful,
12 in progress, one skipped and 12 not yet instantiated. No current failure was
observed. The complete ledger retains current status separately from historical
scientific dispositions; it does not represent the new head as fully green. [R1, C1]

The predecessor f5 full100 aggregate and dependency delta have now completed
and were independently downloaded and checked. The full receipt records
`COMPILER_VERIFIED_FULL_100`: 100 original roots, 28 units, 203 consumer queries,
83 definitions and 18 constructors. All 4,780 source-manifest hashes match the
predecessor checkout, including 1,353 Lean files. The three successful command
logs, compiled exporter hash and all 386 historical reviewed declaration-type
hashes match. The recorded 3,793 declarations use only the standard axiom set.
All 42 exported historical-review source hashes still match unchanged sources.
These are receipt/source checks; this investigation did not rerun Lean. [C1]

The same receipt explicitly has `release_ready=false`, `full_release_accepted=false`
and independent human review `NOT_ESTABLISHED`; RH, Step 4 and the closing
inequalities remain OPEN. The old generated-state gate failed because
`cryptography` was absent, and its summary failed the dependent gate. The new
head installs the already declared requirements. Old aggregate success is not
fresh current-head acceptance. [C1]

Exact root types still govern authority. A theorem `quiet complete observation
-> RH` does not establish quietness. A green wrapper does not turn a saved
`FALSIFIED`, `UNRESOLVED` or `NO_ELIGIBLE_INHERITED_CONTACT` result into a
positive theorem. The original-100 reuse crosswalk records each exact contract,
source, expected-type consumer and physical/domain consumer. [C1]

### 2.2 Drive and attachment coverage

The linked Drive folder was recursively enumerated live: **1,206 unique files
in 152 folders**, with no listing errors and no truncated folder page. The
expanded recensus at 16:57:17 UTC also compared IDs, title, size, modified time, MIME and file/folder kind: no additions, removals or selected metadata changes. This still does not certify unchanged bytes throughout the archive. Current
route dossiers, their original proofs, the latest OPICA papers and amendments,
and the current CI-triage note were reread selectively against the new live
repository pin. A dated Drive note pinned to an older commit does not override
current GitHub evidence. [R2]

The first pass fetched 21 targeted Drive texts. The reading ledger distinguishes
full reading, substantive section review and heading/keyword crosschecks;
the remaining live files have inventory-level coverage in this pass.

The expanded completeness pass fetched 16 more source records, with 13 full readings and three exact-section/schema reviews, and reread the named amendment and route papers. Its 22-record reading ledger preserves these scopes. All 40 direct project attachments now have an explicit disposition, and all 49 original requirements plus WP0–WP7 have a carry-forward map. Neither ledger claims every embedded proof page was reread. [C2, C3]

All 40 named project-source attachments were inventoried and extracted,
including nested archives. The extraction also recovered the October 20
handover's embedded source capsule: 1,466 documentary records, comprising 98
PDFs, 31 Word documents and 1,337 Markdown records. The combined origin ledger
contains 5,792 records and 3,790 unique content hashes, with no extraction
errors. Those are inventory/extraction counts, **not claims to have manually
read every page or proved every archived argument**. The reading ledger
separates substantive review from extraction, indexing, duplicates and inherited
review. The three attached OPICA files and both prior October 25 reports were
read in full. [R2, R3]

The recent state was reconstructed from the v2.9 master, PR292 handover,
Step 4 handovers, A/B/C rounds, the Path D first-contact and ESET-transfer notes,
OPICA's original/followup contracts, and current source declarations. Older
deconvolution, first-contact, canonical-ratio, toolkit and historical-route
documents were used to identify which failed routes had actually acquired a
missing prerequisite. Cross-project material supplies possible methods; it
does not supply a native zeta hypothesis or theorem by analogy.

### 2.3 A naming trap to avoid

The modern **Paths A–D** in this report are the four Step 4 research routes below.
The older CI workflow's **Tracks A–D** use different labels for source/ground
transfer, canonical Schur domination, spectral identification and visibility.
In particular, a green legacy “Track D” job is not a proof of the modern
pole-neutral Path D exit theorem. The workflow appendix preserves its original
names and scopes. A third naming convention occurs in the October 12 requirements: its Track B concerns first-negative propagation and maps mainly to current C/D, not causal B. The 49-ID crosswalk records that distinction. [R1, R2, C2]

## 3. What steps 1–3 now contribute

| Step | Mathematical content now usable | What it does not establish |
|---|---|---|
| 1: fingerprint | An actual off-line zero gives a source-visible, sign-sensitive obstruction with its correct multiplicity and original source | An independent upper bound excluding that obstruction |
| 2: no-hide | Canonical scales and witness-generation results prevent a hypothetical off-line zero from evading every detector | Positivity of every detector or nonexistence of the zero |
| 3: synchronized tracking | The checked consumers keep the same generated state, source, zero, phase/history, multiplicity, transformations and quantitative obstruction; native fixed/slow-source rate theorems identify the retained exponential rate | A change of witness that discards the hard term, or a terminal sign/energy estimate |
| 4: contradiction | Exact conditional interfaces exist for the relevant closing estimates | None of their independent closing premises is proved by the present harvest |

The important new usable information relative to older handovers is the native
rate law. For the literal fixed source family and each fixed `C>1`,

$$
E_d(T;C)=\int_{T-C\log T}^{T}|F_d(t)|^2\,dt,
\qquad
\lim_{T\to\infty}\frac{\log(1+E_d(T;C))}{2T}=\Theta.
$$

Here `Theta` is the actual supremum of nontrivial-zero displacement from the
critical line, with the repository's precise definition. The slow-source
extension prices the schedule `d(T) log(d(T)+2)=o(T)`; it is not an unrestricted
license to send the source order to infinity. The complete fixed two-factor
raw and absorbed high-mask observations retain the same `Theta` rate. No
rightmost-zero or simple-zero hypothesis is required for these conclusions.
[R4]

In particular, the compiled `exists_generatedStep123CompleteOutput` and
`exists_eachPhase_cofinal_generatedStep123CompleteOutput` establish complete
same-packet existence and assembly from an actual off-line zero, any
`0<beta<|Re(rho)-1/2|`, a chosen parity and an arbitrary lateness bound. Cofinality
is available separately for each parity; this does not assert both phases at
one aperture or a witness at every sufficiently large aperture. The construction
is noncomputable and may use `Classical.choice`; it is not an executable search
algorithm. [R1]

Consequently, many earlier “maybe the transformation has made the signal
small” proposals can now be checked decisively. Preservation of the actual
positive rate and an independent strictly smaller upper would contradict each
other. Preservation alone is not the upper.

There is a separate evidence boundary in the large Step123 artifact: its
compiler export is valid for the statements it checks, while its universal
producer/independent-review flags must be reported literally. Do not confuse
those artifact completeness flags with either a failure of a compiled
same-state theorem or a completed universal 44-field release. [R1]

## 4. The four live closing obligations

### Path A — complete signed arithmetic

The target is an independently proved upper on the **complete, correctly
signed arithmetic observation**, including repeated-prime products, finite
palette corrections, collisions, lower masks and all cross terms. The current
rate theorem says its normalized logarithmic rate is `Theta`. A quiet upper
along one cofinal sequence would force `Theta=0`; proving the conditional
consumer again would not.

The earlier October 25 investigation obtains a strict upper on the three unit
axes of one arithmetic trace, with exponent `57/25+o(1)` below `5/2`. That result
has a paper proof and depends on the separately recovered external
seven-eighths theorem. It does **not** bound the whole Eisenstein annulus or
the full signed high-mask observation. The complementary sector and its mixed
terms remain the obstacle. [R5]

The exact balanced continuation is especially instructive. With the actual
finite mollifier `M_{Y,Q}`, corrected zeta factor `Z_Q`, and source transform,

$$\widehat{\mathsf B_Y^\infty}(z)
=\widehat F_m(z)\bigl(1-Z_Q(z)M_{Y,Q}(z)\bigr)^r.$$

At a hypothetical visible zero the factor in parentheses equals one. Increasing
`r`, differentiating the source with a nonzero return factor, or changing a
finite Euler palette does not attenuate the pole. A finite upper cutoff can
remove it from a finite transform, but the omitted continuation retains the
residue. Moving the cutoff past the observation window transfers the problem
to the annular handoff term; it does not estimate that term. [R6]

**Open research target A:** prove a genuinely smaller upper for the literal
complete observation, or a new estimate on its precisely defined complement
that composes with the established axis estimate. An absolute-value estimate
would suffice if it met the required exponent for the complete native object.
A weaker unsigned replacement or toy finite-mask computation does not.

A separate arithmetic-observation branch is now explicit: S10/S17 supply
fixed-direction or phase-complete negative-test margins. A source-matched
nonnegative physical observation with independently smaller total error would
also contradict the hypothetical zero. These linear measure observations have
their own source/recovery scope; they are not the registered high-energy object,
and neither their positivity nor their cheap recovery has been established. [C1, C6, C7]

### Path B — source-specific causal approximation

The old B–Y statement concerns the original completed input at every positive
damping. The proposed October 25 probe is a **different undamped target**.
Keep these two interfaces distinct.

Set `sigma=1/4096`, retain the original probability density `q`, and define

$$j=(D^2-\tfrac14)^2q,\qquad j_+(t)=j(t-\sigma).$$

Use the literal kernels

$$c(t)=\mathbf1_{t\ge0}(-e^{-t/2}+2e^{-3t/2}),$$

$$a(t)=\mathbf1_{t\ge0}e^{-3t/2}
\lfloor e^t\rfloor\bigl(\lfloor e^t\rfloor+1-e^t\bigr),\qquad Tf=a*f.$$

Then `v=c*jPlus`, `w=a*jPlus`, and

$$V(z)=R(z)e^{-\sigma z}J(z),\quad W(z)=A(z)e^{-\sigma z}J(z),$$

$$R(z)=\frac{z-1/2}{(z+1/2)(z+3/2)},\qquad
A(z)=R(z)\zeta(z+1/2),$$

with the removable-pole point treated separately: `A(1/2)=1/2`. An off-line
zero `rho=1/2+lambda`, `delta=Re(lambda)>0`, gives the actual-source separation

$$\|v-Tf\|_2\ge\sqrt{2\delta}\,|V(\lambda)|>0
\quad\text{for every causal }f\in L^2(0,\infty).$$

This zeroth-order witness handles multiple zeros without a derivative lower
bound. Its existence is a useful simplification of the obstruction. The
opposing estimate remains open. [R7]

For `g_n=n^{-1/2}D_{log n}w`, the finite least-squares data are

$$G_N=(\langle g_m,g_n\rangle),\quad b_N=(\langle g_n,v\rangle),\quad q_0=\|v\|_2^2,$$

$$d_N^2=q_0-b_N^*G_N^{-1}b_N.$$

The target column is explicit, with `C=J(3/2)^2/3`:

$$b_1=q_0+C(\zeta(2)-1),\qquad b_n=C\zeta(2)/n^2\quad(n\ge2).$$

**Open research target B:** exhibit actual finite coefficients with residual
tending to zero, or prove the actual `d_N -> 0` by an independent arithmetic
argument. At the classical paper level the generalized strong Nyman–Beurling
theorem identifies the original compact good-kernel version as an RH criterion.
The known optimal-rate theorem of Bettin–Conrey–Farmer assumes RH and an
additional inverse-derivative bound; it cannot close this implication without
circularity. [P1, P2]

The fixed-filter route now has its own conditional global consumer S16:
for the one fixed B of Section 7, finite trials with full filtered residual
norm tending to zero imply RH. Its proof keeps the positive Laplace witness
and does not invert B. This is an alternative sufficient premise to the raw
limit, and the existence of such a sequence remains OPEN. [C2]

### Path C — full continuous contact and original-detector energy

For the **original-detector Schur subroute**, retain the full original detector
and its complete complement. On the same cofinal family produced after fixing
a hypothetical zero and a smaller positive exponent `beta`, the existing lower
obstruction has the form

$$S_n>\tfrac12e^{\beta L_n},\qquad L_n\to\infty.$$

A bound `limsup log(1+max(S_n,0))/L_n < beta` on **that same family** would suffice.
An all-selectors theorem is a stronger optional target, not a logical necessity.
But an inverse-capacity bound without forcing and direct-complement control is
insufficient: a small inverse can multiply a growing forcing vector and leave
exactly the obstructed exponential rate. Aperture and physical-time scales
cannot be identified without the explicit adapter. [R4, R5, R8]

The **full-contact nullsource/exterior-energy subroute** is a distinct
construction; its source is not identified with the original detector above.
The continuous-contact dossiers supply exact exterior/range identities and
cumulative outgoing-energy lower laws. These create alternatives to a
pointwise upper. They do not yet provide a subexponential cumulative upper.
Projected compact-test forcing adapters already exist; rediscovering them does
not eliminate the full-aperture cost or direct term. [R5, R8]

**Open research target C:** independently control the full original-detector
Schur loss, or the exact complete cumulative outgoing energy in the relevant
native contact construction, with an exponent strictly below its proved lower.
Principal-minor or selected-shell estimates require a proved transport to this
object before they are usable.

### Path D — finite pole-neutral first-negative contact

This is a distinct finite boundary problem. The fixed seed lift
`T_a=D^2+aI`, `a=(L/(4 pi))^2`, maps the specified even/odd seed constraints into
the moving pole-neutral carriers. It is not an isometry; both the positive
metric and stiffness must be retained. The relevant contact includes both
parities, ties, inherited kernels, and prime seams. [R9]

With the whole kernel/complement splitting, the Schur germ is

$$F(t)=A(t)-B(t)C(t)^{-1}B(t)^*,\qquad F(0)=0,$$

On a `C^2` cell, with `C(0)>0` and the whole-kernel contact conditions
`A(0)=B(0)=0`, the first derivatives are
`F'(0)=A'(0)` and `F''(0)=A''(0)-2B'(0)C(0)^{-1}B'(0)^*`.
Positive semidefiniteness of the first derivative alone does not control exits
on its nullspace, where arbitrarily high odd-order exits remain possible.
Strict positive definiteness would give a local outgoing positive margin.
Prime seams require their own one-sided regularity and full outgoing germ;
these formulas do not assume two-sided differentiability across a seam.
An asserted finite Taylor order is not an exit theorem.

The archive contains two stronger negative findings that Round 2 must retain:

* A coherent positive modification of prime two produces a pole-neutral
  crossing while preserving the geometric and shape identities. It breaks the
  actual divisor identity, so it refutes a geometry-only argument, not a
  genuinely arithmetic one.
* A global metric-compatible positive-semidefinite transport remainder is
  already falsified for the actual native construction. The small-aperture
  identity `H=-log(L)G+J` makes
  `d/dL tr(G^{-1}H)=-(K-2)/L+O(L)<0`, whereas such a transport remainder would
  force a nonnegative trace. Even the archived `L H` repair has a native
  obstruction. This is not an untested proposal worth simply rerunning. [R9]

**Open research target D:** derive a new restriction from the unchanged native
arithmetic on the entire outgoing Schur germ, or a properly controlled
nonmetric source-dependent mechanism that excludes the generated first exit.
Putting the desired outgoing sign into a packet premise is not a proof.

## 5. What the external seven-eighths result can contribute

The exact pinned external source was fetched afresh in this investigation from
both the user's fork and the official repository. It declares

```lean
theorem OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re
    {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) : riemannZeta s ≠ 0
```

The ordinary Dirichlet L-function companion adds the principal-pole exclusion.
This is not an ordinate-bounded theorem or a renamed zeta object. The earlier
October 25 report contains a detailed historical source/compiled-axiom audit;
this turn verified the current pinned root source and its identity, but did not
recompile the external 2,924-module closure. It uses a different Lean/Mathlib
pin from the native repository. [R5, R10]

At that separately admitted authority level, reflection gives
`Theta <= 3/8`. This yields positive-damping native integrability for damping
strictly above `3/8`. It does not yield the boundary case, all positive damping,
or `Theta=0`. The external detector argument also has its own Hecke-family
uniformity and quantitative geometry. A native zeta rate equality is not an
improved uniform Hecke estimate and does not let the external proof iterate to
the critical line.

Round 2 should keep an optional, separately pinned external-transfer lane. It
must either provide the exact theorem and native adapter under compatible
formal evidence or label the composition as paper-level. The filtered finite
certificate below does not need the external seven-eighths theorem.

## 6. Executed closure attempts and their stopping points

| Attempt | What was used and checked | Result |
|---|---|---|
| Compose exact rate with completed-field decay | Literal source, high-mask correction history, residue-preserving balanced multiplier | The residual retains the original rate; no opposing upper |
| Iterate the external zero-free strip | Exact external root and archived quantitative detector geometry | Only `Theta<=3/8`; the improvement/iteration premise is absent |
| Extend the three-axis estimate to the full trace | Axis proof and source/twist identities | Complement and mixed terms remain unbounded at the required scale |
| Infer zero reality from positive spectral forms | Actual forced Euler/resolvent/sample identities | Equation remains forced; nonreal positive-Gram controls survive |
| Infer causal density from positive contraction | Actual completion and explicit equal-power twin kernels | Generic inference is false; arithmetic target information is essential |
| Optimize the first few raw dictionary columns | Actual delayed source, pulse separation, local divisor identity | Rigorous finite-size lower exceeds the proposed certificate threshold |
| Smooth with the fixed source-preserving filter | Exact multiplier factorization and transported witness | A finite low-height certificate succeeds; global convergence remains open |
| Pass to a bounded-input compactness limit | Actual boundary-zero/source-visibility obstruction | New undamped target is outside the exact range; successful inputs must grow |
| Repair profiles by finite quadratic self-duality | Earlier proof for arbitrary real symmetric finite coefficient matrices | Stated finite distinct-profile repair class is excluded; no claim for infinite or higher nonlinear families |
| Use metric-compatible positive transport | Original Path D deep note and trace identity | Already falsified on actual native source; not reopened |
| Infer Sturm structure from the native positive jump gain | Actual Archimedean density and unchanged prime-two atom | Fresh ordered negative minor, proved below; full resolvent/semigroup questions are separate |
| Use fixed finite derivative sign at a contact | Whole-kernel Schur germ and flat-exit controls | Higher-order/seam branches remain; no D-EXIT theorem |

This is a search for mathematical incompatibility. It does not claim to have
exhausted all possible proofs of RH. A route is rejected only for the stated
mechanism and source/domain class.

In particular, the inherited finite quadratic result uses the actual eligible
profile family at distinct spectral parameters `kappa`, after reflection
duplicates are removed and nonreal conjugate parameters are expressed through
their real blocks. For a real symmetric finite matrix `A`, Fourier self-duality
of the specified quadratic profile forces `A=0` in that class. Repeated-node
jets, infinite families and higher nonlinear repairs are outside this result.
This spectral parameter is distinct from the causal Laplace displacement
`lambda=rho-1/2`; the two coordinates must not be interchanged. [R5]

## 7. A verified finite output from the unchanged source

### 7.1 Why the raw small-dictionary programme must change

The earlier source-specific proof gives, for the residual
`r_x=v-sum x_n g_n` and local divisor discrepancies

$$d_k=\mathbf1_{k=1}-\sum_{n\mid k}x_n,$$

an isolated-pulse inequality through index 2047:

$$\|r_x\|_2^2\ge S^2\sum_{k\in\mathcal K}\frac{|d_k|^2}{k},\qquad
S^2\ge12e^{-1/512}2048^3.$$

If an isolated squarefree index `k` is omitted, Möbius inversion and weighted
Cauchy–Schwarz yield `||r_x||^2 >= S^2/sigma_1(k)`. With
`2047=23*89`, this proves **every initial-segment raw trial with N<=2046 has
residual norm greater than 6900**. The earlier prime-only example gives the
slightly smaller cutoff 2038 and a norm above 7000. The squarefree result is the
stronger support restriction and is retained here. It also applies to a
nonconsecutive dictionary omitting that early squarefree index, however many
late columns are added. [R5]

This bound is finite-scale. It does not imply nonclosure as `N->infinity`,
because the isolated-pulse argument changes once the pulses overlap. The
specified raw regional witness margin is at most `1/12`, so more precision or
a different optimizer cannot rescue these small raw dictionaries.

### 7.2 A fixed filter that retains the exact source

Use the actual causal probability translate `qPlus` and the stable filter

$$B(z)=\frac{z+3/2}{(z+1/2)^5},\quad
b(t)=\mathbf1_{t\ge0}e^{-t/2}\left(\frac{t^3}{6}+\frac{t^4}{24}\right),
\quad\|b\|_1=48.$$

Let `I(z)=(z-1/2)/(z+1/2)`, an isometry on the causal half-line, and

$$u_0(t)=\mathbf1_{t\ge0}e^{-t/2}(1-t),$$

$$h_0(t)=\mathbf1_{t\ge0}e^{-t/2}
\left[(1-t)\lfloor e^t\rfloor+\log(\lfloor e^t\rfloor!)\right].$$

Set `u=qPlus*u0`, `h=qPlus*h0`. The exact identities are

$$Bv=I^2u,\qquad Bw=I^2h.$$

The known common `I^2` is removed isometrically **on this proved range**.
Convolution by the unchanged `qPlus` is an `L2` contraction. Thus a comparison
residual for `u0,h0` provides a valid upper for the filtered actual-source
residual. No unbounded inverse of `B`, source replacement, truncated sinc
product or arbitrary division by an inner factor is used. [R5]

### 7.3 The rational four-column baseline

Take `x=(1,-1,-1,-2/3)`. The full-line unitary comparison maps its energy to the
classical fractional-part residual. The pole moment `sum x_n/n=0` makes that
residual vanish on `x>1`. On changing variables to `y=1/x`, the remaining step
function is

$$C(y)=1-\lfloor y\rfloor+\lfloor y/2\rfloor+\lfloor y/3\rfloor
+\tfrac23\lfloor y/4\rfloor.$$

Its period is 12, with values

$$ (1,0,0,0,2/3,-1/3,2/3,-1/3,1/3,1/3,1/3,-2/3). $$

Hence its energy is the positive series

$$E_0=\sum_{k\ge1}c_{k\bmod12}^2\left(\frac1k-\frac1{k+1}\right).$$

The squared period has mean `13/54`; its centered cumulative sums are at most
`41/54`. Integrating the first 47 cells and applying the periodic Abel tail
bound at 48 gives the exact rational upper

$$E_0\le\frac{315384568453197375401}{4648566756368995059600}
<\frac{17}{250}=0.068.$$

At a hypothetical zero with

$$\frac14\le\delta\le\frac38,\qquad1\le|\tau|\le2,$$

the correctly transported dual witness instead gives

$$\|B r_x\|_2^2\ge
\frac{8192}{93025}\left(\frac{2096767}{2097152}\right)^2
=\frac{4396431852289}{49942416588800}>0.08803.$$

These inequalities are incompatible. They certify the stated rectangle
`3/4<=Re(rho)<=7/8`, `1<=|Im(rho)|<=2`, with the reflected counterpart available
from the functional equation. It is an already-known zero-free low-height
region, used here as a native-channel acceptance baseline. [R5]

The rational arithmetic was independently reconstructed in this turn, including
the period, tail, source margin, a separate 4095-cell bound and the raw-source
obstruction. The attached `verify_round2_controls.py` passes without numerical
quadrature or a floating matrix inverse. Its receipt explicitly distinguishes
the finite arithmetic from the analytic operator proof and from Lean.

### 7.4 What still prevents global closure

The comparison optimization is the classical Nyman–Beurling problem. The
actual source-smoothed Gram is bounded through probability convolution; it is
not equal to the unconvolved classical Gram. The reduced Mellin kernel
`1+log x` also fails the regularity hypothesis of the general good-kernel
theorem at zero. The correct equivalence uses the original strong criterion
and the proved bounded adapters. The separate original compact-source probe
does satisfy the good-kernel hypotheses. [R5, P1]

There is still no independent all-`N` estimate driving the relevant residual
to zero. A finite certificate can exclude its own compact region without
solving that estimate. A long decreasing numerical sequence does not establish
an asymptotic limit.

## 8. Quantitative prefix and error-budget refinements

### 8.1 Prefix constraints are stronger than an unconstrained optimizer suggests

The earlier report already states coordinatewise convergence to the actual
Möbius coefficients. The following is a quantitative implementation refinement,
not a novelty claim for that observation.

Let `alpha` be the left endpoint of the essential support of `w`. On
`[0,alpha+log(M+1))`, all columns with index greater than `M` vanish. The exact
local identity `v=sum mu(n) g_n` therefore gives, for every trial with `N>=M`,

$$r_N=\sum_{n\le M}(\mu(n)-x_n)g_n\quad\text{on that interval}.$$

The finite prefix Gram on this interval is positive definite: take the earliest
nonzero coefficient and use positive `L2` mass arbitrarily close to the first
activation of its column, before the next column starts. Consequently

$$\|x_{1:M}-\mu_{1:M}\|_2^2
\le \frac{\|r_N\|_2^2}{\lambda_{\min}(G_M^{\mathrm{prefix}})}.$$

For the actual source `alpha=0` can be proved from the one-copy sinc product:
retain a finite product prefix with total omitted width less than any given
`h>0`. Its positive-real Laplace transform has a lower bound of the form
`C_K z^(3-K) exp(-sigma z/(K+1))` for `W(z)`. A supposed initial support gap
`h` would give `|W(z)|<=||w||_1 exp(-h z)`, a contradiction. A support-containment
theorem alone is not this exact endpoint proof. [R3]

Use the resulting finite prefix Gram for diagnostics and certified lower
bounds. Do not infer convergence merely because the optimized coefficients
look Möbius-like; raw Möbius truncations have their own obstruction.

### 8.2 A successful raw sequence requires growing input and adaptive cutoffs

The new undamped `v` is outside the exact range of `T`, although closure remains
the open criterion. At a source-visible critical zero of multiplicity `m`, the
earlier boundary-pole argument gives, in the small-error regime,

$$\|v-Tf\|_2\le\eta\quad\Longrightarrow\quad
\|f\|_2\ge(c_*/\eta)^{2m-1}.$$

This statement needs its explicit source-visible critical-zero evidence; it is
not assumed to be an already imported native Lean theorem. The detailed prior
proof gives multiple such evidence routes. [R5]

For a finite source input let

$$A_x=\sum_n|x_n|/\sqrt n,\qquad J_2=\|j\|_2.$$

Then `||f_x||<=J2 A_x`, so the certified **kernel-lag** cutoff error

$$\|(T-T^{[T]})f_x\|_2\le2e^{-T/2}J_2A_x$$

must follow the actual coefficient budget. Requiring that particular bound to
be at most `theta eta` entails

$$T\ge2\log\frac{2J_2A_x}{\theta\eta}
\ge4m\log(1/\eta)+O(1).$$

This is a requirement for the stated certificate bound, **not** a universal
lower bound on true truncation error or computational complexity. A final-output
time cutoff also has to account for delays. The horizon
`S>=T+log N+2sigma` covers the **lag-truncated trial output**, while the
noncompact target has the separate exact tail, for `S>=2sigma`,

$$\|\mathbf1_{[S,\infty)}v\|_2
=\frac{2}{\sqrt3}|J_+(-3/2)|e^{-3S/2}.$$

This tail must also enter the residual budget. A numerical source that does
not preserve the exact annihilating moments cannot reuse that exact formula
without its global source-error allowance. Absolute output time must not be
confused with kernel lag.

Likewise a source approximation with `L2` error `epsilon_j` has sufficient
combined error bound

$$\epsilon_j\bigl(\|c\|_1+\|a\|_1 A_x\bigr).$$

The allowed source error in this budget is of order at most `eta^(2m)` along a
successful raw sequence satisfying the inherited input lower bound. Fixing
precision and then increasing coefficients invalidates the old error bar.
The full derivation and its scope restrictions are included separately.

### 8.3 A changing filter can erase both signal and error

If `B_N=2^(-N)I`, every fixed residual has `||B_N r||->0`, including one separated
from the causal range. Its witness margin shrinks by the same factor. A
variable-filter programme must certify the error divided by the correctly
transported positive margin. The fixed filter in Section 7 avoids that
quantifier trap. This finite synthetic control is executed in the companion
checker; it is not a model of the full zeta construction.

## 9. Fresh source-native obstruction to the immediate TP2 shortcut

The new calculation concerns the **positive off-diagonal jump gain**, with the
literal native density and prime-power coefficients

$$\rho(t)=\frac{e^{-t/2}}{1-e^{-2t}},\qquad c_n=\frac{\Lambda(n)}{\sqrt n}.$$

Its off-diagonal measure is

$$d\mathcal K_R(x,y)=\rho(|x-y|)\,dx\,dy+
\sum_{2\le n\le e^R}c_n(d\nu_{\log n}+d\nu_{-\log n}),$$

where `nu_a(I x J)=|(I-a) intersect J|`. The measure is used only away from the
singular diagonal. It occurs with a minus sign in the full jump stiffness;
the full signed native form is a different object. [R11]

Put `a=log 2`, `d=1/10`, `h=1/1000`, `R>=1` and choose ordered row intervals

$$I_1=[a+d,a+d+h],\quad I_2=[a+2d,a+2d+h]$$

and ordered column intervals

$$J_1=[0,h],\quad J_2=[d,d+h].$$

All four lag intervals lie in `(1/2,1)`. Only the `(1,2)` rectangle meets a
prime-power atom, and that is the actual prime-two atom with overlap `h`.
Every smooth entry satisfies `h^2/2 < b_ij < 2h^2`, while
`c2=log(2)/sqrt(2)>1/3`. Thus the complete ordered matrix is

$$\begin{pmatrix}b_{11}&b_{12}+c_2h\\b_{21}&b_{22}\end{pmatrix},$$

and

$$\det<4h^4-\tfrac16h^3=-\frac{61}{375000000000}<0.$$

The exact source definitions, lag separation, atom normalization, sign and
determinant orientation were independently reviewed. Its rational budget
checker passes. The detailed proof is supplied as
`NATIVE_JUMP_ORDERED_MINOR.md`.

This excludes the immediate argument “the native positive gain is totally
positive, so it supplies Sturm-type crossing control.” It does **not** decide
total positivity for a separately defined full resolvent or heat semigroup;
it does not turn these rectangle tests into legal pole-neutral ground states;
and it proves neither native Weil negativity nor RH. The useful information is
the precise class of arguments that must now be changed or abandoned.

## 10. Revised Round 2 work specification

### 10.1 Preserve the inherited contracts

The original JSON is retained byte-for-byte under `inputs/`. The revision 2.1 JSON copies
all 25 original statements and proposed names. Their inherited acceptance flags
remain false; no new proof is claimed. Cross-references identify the later
deductions that affect their implementation order.

| Inherited IDs | Purpose | Revision 2.1 treatment |
|---|---|---|
| P01–P05 | Literal causal source, stable probe, transforms, zero separation, conditional sufficiency | Foundational; construct actual objects and domains before optimization |
| P06–P12 | Tail/correlation, target column, positive Gram, Schur error, innovations, spectral norm, conditional limit consumer | Keep; exact finite solver is research infrastructure, not the closing estimate |
| P13–P16 | Local Möbius inverse, divergent integer truncation, safe cutoff, zero barrier, noncausal leakage | Mandatory controls when their operation is used; no unqualified global integer sum |
| P17–P19 | Confluent zero witnesses, simultaneous lower bounds, primal certificates | Prefer the single-witness/primal certificate first; do not block on matrix inversion |
| P20–P23 | Correct classical adapter, product margin, regional certifier, certified source approximation | Keep original compact kernel distinct from filtered comparison; carry all error budgets |
| P24–P25 | Classical necessity and resulting iff | Optional true formalization/import; never add as project axioms |

### 10.2 Explicit proposed supporting amendments

These are proposed additions for review, not silent promotions into the frozen
PR294 contract or a claim of 17 new discoveries. The revision 2.1 JSON records exact
statements, source references, dependencies, forbidden substitutions and
acceptance fields.

| ID | Supporting amendment | Origin/status |
|---|---|---|
| S01 | Isolated-squarefree dictionary obstruction; exact activation endpoint; all-prefix quantitative Möbius constraint | Inherited finite obstruction and coordinatewise result; strengthened prefix formulation DERIVED here |
| S02 | Pole moments `P_N(1)->0`, `P_N'(1)->1` with bounded-functional error bounds | Earlier October 25 paper deduction |
| S03 | Completed-output Bernoulli tail and asymptotically free leading-tail neutrality | Earlier October 25 paper deduction |
| S04 | Literal stable filter, exact `I^2` factorization and valid range isometry | Earlier October 25 paper deduction |
| S05 | Full-line classical comparison with negative-time cancellation and unchanged `qPlus` contraction | Earlier October 25 paper deduction |
| S06 | Transported filtered witness and exact four-column regional baseline | Earlier paper proof; finite arithmetic independently rerun here |
| S07 | Exact undamped nonrange and multiplicity-aware input-cost lower bound | Earlier paper proof with explicitly separated critical-zero evidence |
| S08 | Coefficient-dependent source/lag/output budgets and variable-filter normalized margins | DERIVED implementation refinement here; no universal complexity claim |
| S09 | Finite quadratic Fourier-self-duality obstruction in the precise eligible profile class | Earlier October 25 proof; no infinite-family extension |
| S10 | Fixed-witness imaginary-direction positive test and error threshold | Attached deep search; no positivity-producing arithmetic approximant supplied |
| S11 | Exact positive-damping abscissa and equivalence audit of actual native closing cuts | Attached deep search and current rate theorems; boundary unclaimed |
| S12 | Equal-power positive causal twins and full-line/causal distinction | Attached deep-search control; explicitly synthetic |
| S13 | Native jump-gain ordered negative minor | Fresh DERIVED proof and exact rational budget check in this pass |
| S14 | Every convergent scalar normalization of CT1 has limit aT; order-zero limit is zero | Inherited paper consequence of current native limit/nonmeasure theorem |
| S15 | Fixed-aperture legal approximation with exact pole-neutral repair | Inherited paper composition; no effective cutoff or no-exit sign |
| S16 | Global fixed-filter native approximation implies RH | Conditional consumer; its approximation premise remains OPEN |
| S17 | Three adapted positive tests and four explicit phase-complete bumps | Inherited paper derivations; exact height, independence and cost scopes retained |

The optional **C2/C3/C4** extension records are separate from these 17 amendments.
C3 includes the explicit epsilon/window correction and normalized regularizer.
The existing sharp C1 and maximal actual-square repair theorems are reused.
The JSON also contains 25 scoped control records, 13 deferred/research
dispositions and a complete proposed-module manifest. See Section 15. [C1–C8]


### 10.3 Build order chosen for mathematical information

**Milestone 0 — pin and native identity.** Freeze the inspected tree, copy the
original proposals unchanged, and bind each reused declaration to its full
type/source hash. Keep the current-head aggregate and release status separate
from the available mathematical slice. No theorem count changes during this
step.

**Milestone 1 — establish the actual probe and its obstruction.** Implement
P01–P04 and the independently typed physical consumers. Check causal delay,
one-copy `Q`, removable pole, multiplicity and the distinction from the old
completed input. P05 is a conditional wrapper and must stay labelled as such.

**Milestone 2 — reproduce the finite filtered baseline.** Implement S04–S06
and the conditional global consumer S16. The direct baseline has no P19 dependency; P19 remains a later general certificate. Replay the exact rational certificate
and give a native theorem for the specified compact rectangle. This is a
demonstration that the pipeline can issue a sound output, not a global proof.
The revision explicitly removes the unnecessary S06-to-P19 dependency. The finite baseline does not require implementing a huge raw Gram matrix,
all multi-zero jets, or an interval inverse.

**Milestone 3 — install failure controls and calibrated budgets.** Add S01,
S07–S08 and the relevant truncation/leakage controls P13–P16. Freeze separate
kernel-lag and absolute-output cutoffs, coefficient budgets and transported
witnesses in the receipt. Reject the raw small-dictionary and moving-filter
false positives deliberately.

**Milestone 4 — study the actual asymptotic obstruction.** Complete P06–P12
and the source-correct finite certifier as useful. Seek an explicit coefficient
family with an independently proved residual bound, allowing the required
input growth, or an independent upper on the optimal remaining residual.
Ill-conditioning, monotone decrease and repeated finite successes are recorded
as observations, never as the terminal estimate. Optional P17–P18 and P24–P25
should be built only when they answer a concrete remaining question.

**Parallel mathematical lanes A/C/D.** Each lane must target the exact OPEN
statement in Section 4. Use the current rate, first-contact and source theories
as inputs. If a candidate bound only reproduces the same positive rate, or if
its decisive premise is the desired sign, reject it before a large Lean build.
The global target can close through one valid route; the specification does
not require solving all four.

### 10.4 Experiments with meaningful acceptance rules

| Experiment | Required output | Stop/reject condition |
|---|---|---|
| Filtered regional primal | Rational coefficients; exact/certified energy upper; transported regional lower; all source and domain identities | `upper >= lower` gives NO_CERTIFICATE, not a disproof of the criterion |
| Raw prefix diagnostic | Verified prefix Gram lower eigenvalue and discrepancy from exact Möbius coefficients | A proposed tiny residual contradicts its own prefix lower bound |
| Lag/source stability | One absolute error budget using actual coefficients and filter | Old error bar reused after coefficients, source or horizon changed |
| Complete high-mask estimate | Full signed tuple decomposition with masks, collisions and complement retained | Bound applies only to unit axes, an insufficient unsigned majorant or an inactive small-`T` toy corridor |
| Fixed-family Schur upper | Same produced family, original complement, exact aperture/time conversion | Forcing/direct term omitted, or upper exponent not below lower exponent |
| D exit candidate | Whole-kernel, both-parity native germ with seams and inherited kernels | Geometry-only argument also proves the known modified-prime control impossible |
| Native jump TP proposal | Exact definition of gain, stiffness, compression, resolvent or semigroup | Conflation with the explicitly negative ordered gain minor |

The fixed log-slack schedule itself becomes arithmetically huge before its
large-`T` lower-factor cutoff is nontrivial. A small brute-force pilot cannot
be sold as a test of the proved cofinal asymptotic regime. Symbolic identities
and analytically priced remainder estimates should precede large enumeration.

## 11. Proof and claim acceptance

Every new Lean claim needs a real compatible source build, independently stated
expected type, physical/native domain consumer, transitive standard-axiom
audit, and an exact source-pinned receipt. A copied signature-only check is not
independent review. No project axiom, `sorry`, changed toolchain, substituted
source or hidden desired conclusion is permitted.

The parent mathematics and original PR294 contracts remain frozen. Any change
to a mandatory statement, domain or dependency must be a visible versioned
amendment with a mathematical explanation. Supporting results do not inflate
the 100-root count. Optional classical transfers remain optional until their
full proofs are available.

A finite certificate's analytical theorem, rational/interval verifier and
source receipt have different roles. All three are needed for its claimed
scope. A finite verification says nothing about unbounded height unless a
separate covering or asymptotic theorem has been proved.

The status vocabulary is fixed:

* **PROVED:** exact existing statement with the stated formal/compiler evidence.
* **DERIVED:** a supplied mathematical argument, not newly Lean-compiled.
* **LEAD / HYPOTHESIS:** an idea or unproved construction to test.
* **EXPERIMENTAL SIGNAL:** bounded computation or numerical observation without
  the needed general theorem.
* **OPEN:** no established closing statement.

## 12. Post-green research assessment

### What became formally true

The current checked source preserves the exact 100-root OPICA slice and its
same-state, source-rate, signed-measure, forced-profile and truncation controls.
No Lean mathematics changed between the attachment pin and the inspected head.
The completed predecessor receipt has been independently inspected, while fresh current-head checks remain incomplete. This
investigation supplies no new compiled theorem.

### Workflow harvest

Every declared current-head job is listed with its execution status, scientific
scope, class, historical result and source URL in the companion harvest. Fresh scientific output was not reread for every new running job; that distinction is explicit. The
important preserved outcomes include successful frozen boxes, unresolved
contact/Schur targets, the altered-prime crossing, the signed-ray falsification
and the absence of eligible inherited contacts. Pending jobs are not passed by
association.

### What changed

The revised plan uses the actual finite obstruction to avoid an unproductive
small raw-dictionary build. It promotes the already derived filtered native
certificate to the first measurable milestone, adds all-prefix quantitative
diagnostics and adaptive error budgets, and excludes the immediate native
jump-gain TP2 shortcut. These are changes in the research/build specification,
not a claim that the terminal approximation theorem has appeared. Revision 2.1 additionally restores S14–S17, the corrected optional separator lane, source-specific controls, historical requirements and all deferred routes identified by the omission audit.

### Upstream implications

Keep the small source/causal probe abstraction separate from the global closure
premise. Source support containment must not stand in for the exact activation
endpoint. Kernel-lag cutoffs must not stand in for absolute output cutoffs.
Positive power data must not stand in for phase-sensitive causal range data.

### Downstream implications

The filtered verifier can produce rigorously scoped regional certificates.
The prefix and input-budget constraints can reject false numerical successes
before a proof campaign. The rate theorem tests any proposed arithmetic upper
against the correct zero displacement. Fixed-witness quantifiers can reduce
unnecessary uniformity demands in a genuine contradiction argument.

### Resurrected routes

Source-preserving causal approximation and fixed-witness comparison remain
worth pursuing with their exact new adapters. Paths dependent only on the
formerly missing native rate law can now be evaluated using it. Geometry-only
exit control, global metric-compatible PSD transport, equal-power positivity,
raw integer truncation and finite quadratic heat repair remain excluded in
their proved classes.

### New RH-relevant clues

The useful clues are the explicit mixed target column, complete retained rate,
the finite filter/witness baseline, quantitative early-coefficient rigidity and
the shrinking admissible class of contact mechanisms. They point toward an
arithmetic estimate retaining phase and the actual source. None is itself that
estimate.

### Falsification checks

Use the unchanged prime-two and altered-prime controls with their distinct
scopes, the forced Gram model, positive causal twins, raw finite-size barrier,
divergent integer completion, critical-zero input cost, variable-filter ratio
trap and high-order contact controls. Failures must remain in the ledger rather
than being hidden by a narrower test family.

### Highest-leverage next moves

First formalize and certify the actual filtered finite output and its compulsory
controls. In parallel, pursue one new **complete signed arithmetic estimate**
or **same-family outgoing-energy/germ restriction** that is not merely another
equivalent statement of RH. Require the candidate to survive the relevant
native and synthetic controls before expanding implementation. The global
closing estimate remains the research task.

## 13. Source guide

**R1.** `PR294_LIVE_HARVEST_2026-10-25.md`, `WORKFLOW_HARVEST.json`, exact source
and artifact receipts supplied in this package. Live PR and pinned tree:
<https://github.com/HMarcusWH/zeta-23-lean/tree/416aec21d4d6634675639b5397cc300d1f826e34>.

**R2.** `drive_archive_report.md`, `live_inventory.json`, `drive_reading_index.json`.
Live root: <https://drive.google.com/drive/folders/1FwRkN6sbJ4_Fhrqe53wpsJtByD2RXILb>.

**R3.** `history_math_audit.md`, the attachment coverage ledger, and the
quantitative prefix-support supplement in this package.

**R4.** Current native declarations:
[NativeWindowRate.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/416aec21d4d6634675639b5397cc300d1f826e34/Zeta23/OPICAFollowup/NativeWindowRate.lean),
[MovingSourceWindowRate.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/416aec21d4d6634675639b5397cc300d1f826e34/Zeta23/OPICAFollowup/MovingSourceWindowRate.lean),
[Consumers.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/416aec21d4d6634675639b5397cc300d1f826e34/Zeta23/OPICAFollowup/Consumers.lean),
[Step4OutputSufficiency.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/416aec21d4d6634675639b5397cc300d1f826e34/Zeta23/ExceptionalZero/Step4OutputSufficiency.lean).

**R5.** Earlier 25 October complete paper investigation, retrieved in full:
[Step4_Closure_Investigation_2026-10-25.html](https://chatgpt.com/library?file_id=libfile_c42a304601a081919008dc6eff538c57&account_id=personal).
Its proof records are inherited paper evidence, not newly compiled authority.

**R6.** `RH_Final_Gap_Residual_and_Handoff_Audit_2026-10-20`, exact Drive source
<https://drive.google.com/file/d/1eO_QNnwswL_VzTjIgbWGgk0MUQLYIiEW/view>.

**R7.** The three attached October 25 OPICA documents, preserved under `inputs/`:
deep search, Round 2 research/specification, and the original theorem contracts.

**R8.** `PRO_C_C05_Round4_Native_Exterior_Observability_2026-10-12`,
<https://drive.google.com/file/d/1Vg5dsSBQ3kum3LTfzTgX8E5WQ9B4wvw6/view>,
and the source-pinned original-detector complement/forcing modules linked by R1.

**R9.** `PATH_D_START_HERE_2026-10-14`, `ESET_PATH_D_DEEP_RESEARCH_NOTE_2026-10-14`,
the original finite pole-neutral contact investigation, and the transfer ledger;
exact IDs/hashes and reading disposition are in the Drive/attachment ledgers.

**R10.** Official external root source at its separate pin:
[OAI DirichletL/Nonvanishing.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean).
Source blob `46c67f4000906b1391a471d6e6396ac0da3c16a5`; historical compiler
evidence is reviewed in R5, Appendix 9. No fresh external build is claimed here.

**R11.** Native density/prime coefficients:
[Components.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/416aec21d4d6634675639b5397cc300d1f826e34/Zeta23/CCM/Components.lean),
and R8, Proof record J. Full new proof and rational receipt are included.

**P1.** L. Báez-Duarte, *A general strong Nyman–Beurling criterion for the
Riemann hypothesis* (2005), <https://arxiv.org/abs/math/0505453>.

**P2.** S. Bettin, J. B. Conrey and D. W. Farmer, *An optimal choice of Dirichlet
polynomials for the Nyman–Beurling criterion* (2012),
<https://arxiv.org/abs/1211.5191>. The optimal-rate statement is explicitly
conditional on RH and an additional inverse-derivative bound.

## 14. Reproduction

Run the two exact finite-control scripts with ordinary Python 3:

```text
python3 verify_round2_controls.py --output exact_control_receipt.json
python3 verify_native_jump_minor.py
```

The first verifies the inherited regional certificate arithmetic and the new
implementation controls. The second verifies the rational budgets in the
fresh native jump-minor proof. Neither command compiles Lean. The package
manifest binds the inspected source pin, inherited inputs, reports, contracts
and reproducible checks. Before a future proof build, refresh live PR/CI status
and compare mathematical source hashes; do not transplant a receipt across
changed source bytes.


## 15. Completeness revision 2.1

**25 October 2026.** This revision addresses the request to recheck the repository, project files and linked Drive folder for omissions from Round 2. **Step 4 and RH remain OPEN. New Lean declarations compiled in this investigation: 0.**

### 1. Audit outcome

The delivered v2 omitted useful mathematical consequences and did not give every inherited obligation an explicit destination. Revision **2.1** corrects those omissions while preserving the original 25 proposed contracts and the original 100 repository roots.

The revised specification now has **17 supporting amendments**, up from 13. The four added records are CT1 scalar-limit classification, the finite pole-neutral approximation composition, global sufficiency of the fixed filtered approximation, and phase-complete positive-test observability. These are proposed formalization records for existing paper deductions or compositions. Their addition is not a claim of four new discoveries or four newly compiled theorems.

The revision also carries the optional C2/C3/C4 programme, a control registry, the deferred source-specific research lanes, the original 49-requirement applicability crosswalk, WP0–WP7, the 100-root reuse map, and a complete proposed module map. Each audit finding has a concrete disposition in `disposition_matrix.json`. A DEFER entry preserves an unresolved obligation; it does not certify its conclusion.

The main report and JSON remain the authoritative current handoff. The exact delivered v2 is preserved under `round2_completeness/baseline_v2/`, and the three original OPICA inputs remain unchanged. No repository or Drive source was modified.

### 2. Evidence refreshed and its limits

#### Repository

The source pin is now **`416aec21d4d6634675639b5397cc300d1f826e34`**, tree **`0506bca8ffe613e9cd9ab844650a1141d4494f66`**, based on `d53dd70d38b0762af130b1d19b795af259f505f5`. Compared with the delivered `f5bafbc` pin, the change adds two workflow setup lines that install declared framework requirements and refreshes eight generated metadata files. **Lean sources and dependency pins are unchanged.** The comparison and source identity checks are included. [C1]

The completed predecessor aggregate was downloaded and inspected independently. Its recorded status is `COMPILER_VERIFIED_FULL_100`: 100 original roots, 28 acceptance units, 203 consumer queries, 83 required definitions and 18 constructors. All 4,780 source-manifest entries match the local predecessor checkout, including 1,353 Lean files. The three recorded successful command-log hashes, compiled exporter hash and 386 historical reviewed declaration-type hashes match. The receipt records 3,793 declarations using only the three standard axioms. This is inspection of the actual receipt and its bindings; Lean was not rerun. [C1]

That same receipt explicitly leaves `release_ready=false`, `full_release_accepted=false`, independent human review `NOT_ESTABLISHED`, and RH, Step 4 and the independent closing inequalities OPEN. The predecessor's generated-state gate failed because `cryptography` was absent; its summary failed the dependent gate. Its full100 and dependency-delta jobs succeeded. These distinct outcomes are preserved. [C1]

At **17:07:17 UTC / 18:07:17 Europe/Stockholm (CET)** on 25 October, the new head had 22 workflow runs and 76 declared jobs: **51 successful, 12 in progress, one skipped, and 12 not yet instantiated**. There were no current failures at that snapshot. The full current ledger retains every job, its run and event, and the distinction between current execution status and historical scientific output. Neither old success nor unchanged sources is represented as a completed fresh aggregate. [C1]

The reuse crosswalk accounts for **100/100 original roots** across 40 mathematical modules, including their frozen contract, declaration location, source hash, independent expected-type consumer and physical/domain consumer. All 42 historically reviewed exported source hashes still match. This avoids rebuilding old infrastructure under a new name while keeping exact theorem hypotheses visible. [C1]

#### Project files and Drive

All **40 direct project files** have explicit dispositions. Their inherited extraction ledger accounts for nested archives and duplicates; it does not claim a new semantic rereading of every embedded page. This pass read the original operating rules, the complete selected CT1, finite-neutral, iteration, Euler-product and positive-root arguments, the relevant historical build specification, the requirement register, and the specific older source adapters used by this revision. The project audit records proof review separately from acquisition and inherited review. [C2]

The Drive folder was recursively relisted at **16:57:17 UTC**: **1,206 unique files in 152 folders**, zero listing errors. Comparing IDs, title, size, modified time, MIME and file/folder kind found no additions, removals or selected metadata changes. This is a metadata comparison, not a byte-hash comparison of all 1,206 files. [C3]

The expanded pass fetched 16 source records: 13 read in full and three by exact section or schema. It also fully reread the post-green amendment, latest extracted B04 paper and Path D start, and reviewed the consolidated final paper's analytic/sampling/acceptance sections and C05's original exterior-closing section. The combined reading ledger has 22 records for this expanded pass. The original P0 manuscript, every R1/R2 proof page and the entire historical A/C archive were not reread end to end. The appropriate conclusion is that all material findings identified in this source-to-contract audit now have a disposition—not that every archived argument has been independently re-proved. [C2, C3]

### 3. Four restored supporting contracts

#### S14 — all scalar limits of the CT1 family

The native theorem already proves, on every Schwartz test,

\[
L^{-2}\nu_L\longrightarrow T,
\qquad
\nu_L=D_L+D_{-L}-2\cosh(L/2)D_0,
\qquad
T=\sum_{n\in\mathbb Z}(n^2\delta_n''-2n\delta_n').
\]

It also proves that $T\ne0$, that it is not of order zero near any nonzero integer, and that normalized local variation diverges. The missing Round 2 consequence is the full scalar classification:

\[
L_j\ne0,\ L_j\to0,\ c_j\nu_{L_j}\to U
\quad\Longrightarrow\quad
\exists a\in\mathbb C:\ c_jL_j^2\to a,\quad U=aT.
\]

Choose a Schwartz test \(\phi_0\) with \(T(\phi_0)\ne0\). The quotient

\[
c_jL_j^2=
\frac{c_j\nu_{L_j}(\phi_0)}{L_j^{-2}\nu_{L_j}(\phi_0)}
\]

converges to a scalar $a$. Apply the product limit on every other test to obtain $U=aT$. Consequently a limit that is locally of order zero on the real line, or on a neighborhood of any nonzero integer, must be zero. Order zero only near the origin would not be enough. No monotonicity of $L_j$, positivity of $c_j$, or common variation assumption is needed for this particular scalar classification. It says nothing about changed families, nonscalar transformations or added counterterms. [C2, C4]

The related controls are also explicit: for $0<L<\log2$, the native positive sinc mass is $2e^{-L/2}(1-e^{-L})$, its ratio to $L$ tends to 2, and its ratio to $L^2$ diverges. Sinc squared is not Schwartz, so its existing integrability argument must be retained. The near-gap atoms at \(\pm e^{-L}\) violate the exact unit gap. The separate synthetic sequence $n(\delta_{1/n}+\delta_{-1/n}-2\delta_0)$ shows why generic Schwartz convergence does not imply convergence on all continuous compact tests without common variation. The native controlled $C_c$ upgrade is already available with that premise. [C1, C4]

#### S15 — finite approximation with exact pole-neutral repair

The project has a paper composition that was not exposed as a Round 2 contract. Fix $L>0$, write $a=(L/(4\pi))^2$, and use the legal centered stencils

\[
e=(1,-4,6,-4,1),\qquad o=(-1,2,0,-2,1).
\]

For \(\ell_0(u)=\sum u_n/(a+n^2)\) and \(\ell_1(u)=\sum nu_n/(a+n^2)\), their constraint matrix is diagonal:

\[
\ell_0(e)=\frac{24}{a(a+1)(a+4)},\qquad
\ell_1(o)=\frac{-12}{(a+1)(a+4)},\qquad
\ell_1(e)=\ell_0(o)=0.
\]

After centered padding to a common cutoff, the correction

\[
\widetilde u=u-\frac{\ell_0(u)}{\ell_0(e)}e
                -\frac{\ell_1(u)}{\ell_1(o)}o
\]

is exactly legal and pole-neutral. The actual native odd witness is $De=2o$; its denominator must be scaled consistently. The physical exponential-moment adapter makes the correction coefficients tend to zero when legal approximants converge to a neutral compact target in \(\|f\|_1+\|f''\|_1\). WCONT then preserves a strict negative margin. [C2, C5]

The resulting existential producer is

\[
\neg RH\Longrightarrow
\exists L_0>0\ \forall L>L_0\ \exists K\ge3\ \exists u\ne0:
\quad u\text{ legal and neutral},\quad Q_{L,K}(u)<0.
\]

At least one parity component is negative after splitting. It is not a claim that both are negative or that strict even can be selected beforehand. This producer provides neither an effective cutoff nor a uniform aperture rate, the quantitative detector schedule, a selected-ground identity, or the outgoing first-boundary sign. Those remain separate obligations. [C2, C5]

#### S16 — the global consumer for the fixed filtered programme

The practical milestone already used

\[
B(z)=\frac{z+3/2}{(z+1/2)^5},\qquad
r_x=v-\sum_nx_ng_n.
\]

The terminal specification named only the raw residual. It now also states the sufficient filtered premise:

\[
\exists x^{(k)}\text{ finite}:\quad
\|Br_{x^{(k)}}\|_{L^2(0,\infty)}\to0
\quad\Longrightarrow\quad RH.
\]

Indeed, at an actual right zero \(\lambda=\rho-1/2\), with \(\delta=\Re\lambda>0\), every finite trial obeys

\[
\|Br_x\|_2\ge\sqrt{2\delta}\,|B(\lambda)V(\lambda)|>0.
\]

The dictionary vanishes at that evaluation, while the exact native source and fixed filter do not. This proof uses bounded causal Laplace evaluation. It requires no bounded inverse of $B$ and does not infer a raw norm estimate. The existence of a convergent filtered sequence remains OPEN. Raw and fixed-filter approximation are now explicitly alternative sufficient premises. [C2]

#### S17 — phase-complete positive observations

Three distinct statements must coexist:

| Construction | Exact scope | Missing ingredient |
|---|---|---|
| S10 fixed imaginary direction | One actual offcritical witness, every positive height | A native nonnegative observation of that fixed direction with sufficiently small error |
| Three adapted tests | One fixed independent actual Re/Im pair with nonreal \(\kappa=\rho(1-\rho)\); no height or simple-zero restriction | Effective test/recovery cost and a native positivity/comparison construction |
| Four explicit first-cell bumps | \(\gamma>2\pi/\log2\), with explicit points and margin | The same source-matched positivity/comparison construction |

For a fixed independent $n$-dimensional actual real zero-jet measure span, the existing positive-only-zero theorem and finite-dimensional cone separation give $n+1$ nonnegative smooth compact off-lattice tests realizing the covectors $e_1,\ldots,e_n,-\sum e_i$. Therefore every nonzero coefficient direction has a negative test pairing with a fixed norm margin. The actual canonical pair gives $n=2$, hence three adapted tests. This is an inherited paper consequence, not a separately compiled realization theorem. It has no uniform support, height, seminorm or recovery-cost bound. [C1, C6]

The four explicit construction retains its stronger height premise. With $q=\delta+i\gamma$, $Z=(1/4-q^2)/q$ and $u_j=j\pi/(2\gamma)$, the four values are $iZp_1,-Zp_2,-iZp_3,Zp_4$, where the positive $p_j$'s alternate the corresponding hyperbolic cosine and sine factors. Thus

\[
\min_j\Re(cg_\rho(e^{u_j}))\le-\eta_\rho|c|,
\qquad \eta_\rho=|Z|\min_jp_j/\sqrt2>0.
\]

The explicit derivative bound gives four nonnegative unit-mass bumps with a margin at least \(\eta_\rho|c|/2\). If actual nonnegative observations approximate these pairings and \(|c_T|\ge a_0>0\), their maximum error cannot be smaller than \(\eta_\rho a_0/2\). Obtaining those observations and beating that threshold is the open arithmetic task. Complex phase, finite Fourier parity and choice of source are not interchangeable. [C6, C7]

### 4. Optional separator work restored with corrections

**C1 is already available.** Reuse the sharp $2\operatorname{arsinh}(\|u-v\|/2)$ logarithmic norm comparison, scalar equality and positive-part companion in a seminormed additive commutative group. It needs neither an inner product nor completeness. It supplies no arithmetic upper on its own. [C1, C3]

**C2 remains an optional paper extension.** For a real signed Radon measure of polynomial total-variation growth, exact Fourier self-duality, zero restriction to \((-1,1)\setminus\{0\}\), and nonnegative off-integer restriction, prove that the measure equals its origin mass times the integer comb. This extends the old linear-growth/full-origin-gap interface. It must not accept generic tempered distributions containing atom derivatives. [C3, C8]

**C3 must use the corrected smoothing domain.** The full contract defines a real even nonnegative smooth compact probability regularizer \(\phi\), its autocorrelation \(\psi\), the triangle \(\Delta\), and

\[
f_\epsilon=\Delta*\psi,\quad
w_\epsilon=\operatorname{sinc}^2|\widehat\phi|^2,\quad
P_\epsilon-N_\epsilon
=D_\epsilon+\int f_\epsilon\,d\nu-\nu(\{0\}).
\]

The probability normalization is essential: $w_\epsilon(0)=1$. All pairings and the actual Jordan parts are part of the statement. The bound with smoothing cost \(\epsilon|\nu|([-2,2])\) requires **\(0<\epsilon\le1\)**. Otherwise enlarge that variation window to \([-1-\epsilon,1+\epsilon]\). The original unrestricted version has a repository counterexample at \(\epsilon=4\), which is retained with all seven original controls. [C3, C8]

The regional version retains $R\ge1$, $0<d\le1/2$ and \(\epsilon\le(2\pi R)^{-1}\), with coefficient \(d^2/(\pi^2R^2)\). A native application must separately construct the genuine order-zero source measure, prove an energy-to-observation inequality, and independently bound negative mass, tested Fourier defect, gap deficit, smoothing variation, the $b_T,c_T$ factors and any \(\pi^2R_T^2/d_T^2\) observation penalty. Its valid conclusion is \(\log(1+E_T)=o(T)\), not a literal equality $E_T=\exp(o(T))$. These native premises remain OPEN. [C3, C8]

**C4 is not missing square infrastructure.** The actual square no-repair theorem is already stronger than the old polynomial-growth proposal: it permits arbitrary locally finite complex lattice corrections with a tempered distribution agreeing on compact Schwartz tests, including addition of a selfdual tempered distribution. No total-variation-growth assumption is required. Reuse it. The generic fixed-measure C4 corollary can remain optional under all C2 hypotheses. Canceling one tested defect with a lattice atom is not full distributional self-duality. [C1, C3]

### 5. Failure controls and source identities restored

The revised control registry includes the following previously missing controls, with their proof or replay status:

- **Fixed-filter Euler products still diverge globally.** Actual finite prime-product dictionary trials agree with $Bv$ before the next-prime logarithm, yet for every fixed $0\le\epsilon<1/2$ their weighted norms have a lower growth bound of the form \(\exp(c_\epsilon P^{1/2-\epsilon}/\log P)\). Local exactness and this fixed filter do not rescue that sequence. Freely optimized coefficients remain a different question.
- **Correct Landweber descent can leave a residual.** The adjoint iteration converges to the target's projection onto \(\ker T_\epsilon^*\). The missing progress law or zero projection is an open input. The no-adjoint iteration has an inherited native frequency falsifier at frequency 12 for damping 0 and $1/100$; that enclosure was read, not rerun in this pass.
- **Forward positivity does not supply arbitrary positive convolution roots.** For the current triangular completion, the inverse Laplace measure of the logarithmic derivative contains the elementary density $e^{-t/2}+e^{-3t/2}-e^{t/2}$, which is negative on the atom-free interval \((\log2,\log3)\). The inherited argument excludes arbitrarily high positive roots of each fixed probability tilt. It makes no claim of an off-line zero.
- **Retain the original observation and continuation controls.** Coupled-Gram collision, raw-energy versus norm-first separation, history recovery cost, positive forced Gram at nonreal parameter, real/duplicate-node degeneracy, all affine histories, connected continuation, boundary-error equality and zero-radius failure remain explicit. The native jump minor and the metric-compatible transport falsification keep their exact scopes.

These controls are not new original roots. The register distinguishes existing native theorems, paper deductions, inherited numerical enclosures, and synthetic controls. Compiler rejection for a missing hypothesis is not described as a mathematical counterexample. [C1, C2]

The source crosswalk is now formula-level:

| Construction | Source and target | Valid transfer boundary |
|---|---|---|
| B02–B04 | $h=(D^2-1/4)^2(q*q)$, two copies of $Q$; target \(-R_{\mathrm{old}}H\zeta'\) | $h=q*j$ is a paper convolution adapter; a suitable upper transfers one way with the right horizon enlargement |
| October 13 triangle | One-copy $j$, target \(-RJ\zeta'\) | Rational normalization change can be causally invertible; it does not remove the \(\zeta'\) numerator |
| October 25 Round 2 | Literal delayed $j_+$; $V=RJ_+$, $W=RJ_+\zeta$ | New target needs its own physical identity and visibility proof |

Here $R_{\mathrm{old}}=(z-1/2)/[(z+1/2)(z+1)]$ and $R=(z-1/2)/[(z+1/2)(z+3/2)]$. The boundedly causally invertible multiplier $(z+1)/(z+3/2)$ changes both old operator and old input consistently; it does not equate different source problems. [C2]

### 6. Deferred lanes remain visible

The specification retains these as research options with exact source requirements:

| Lane | Missing task or constraint |
|---|---|
| Autocorrelation logarithmic-window covariance | Independently bound the full signed off-diagonal; retain the old two-copy source and one-way adapter |
| Fixed-frequency Suzuki orbit | Prove its actual local-work/subexponential upper; preserve the historical source and matched instability controls |
| Corrected prime-prefix OPEN-X | Bound the global residual subpolynomially with the exact escaping cutoff pulse and all prime powers |
| Forced-profile boundary amplitude | Supply an independent incompatible constraint on the actual \(\zeta(\rho)/b_\rho\); positive sampling alone is insufficient |
| C05 cardinal/exterior representer | Prove exact annihilation on the required superlinear set of distinct simple critical ordinates in the actual form domain |
| R002 and RES/TAIL/COFINAL | Preserve alternative quantifiers; block-level negative index is not global pair unmasking |
| Moving sextic OPEN-S | Optional alternative to the fixed two-factor rate route; not a new mandatory prerequisite |
| Finite-rank and growing-span recovery | Prove bounded recovery/common variation at the new scope; fixed finite-basis results do not provide uniform limits |
| Contact adapters and inverse estimates | Preserve same-state forcing, whole complement, endpoint/seam conditions and the missing trial excess |

The earlier $57/25$ unit-axis estimate still does not bound the full high observation. Its row-counting obstruction survives even if the individual constants become uniform; the full mixed/complement estimate remains missing. [C2, C3]

The stronger reported **Baiying Liu $0.874957019420\ldots$** benchmark is now recorded as **UNVERIFIED IN THIS INVESTIGATION**. The supplied primary manuscript and the old audit's explicit non-rebuild statement were traced. It does not replace X01's independently source-checked $7/8$ input. The similarly named October 11 `liu_scalar_*` receipts concern a compact-Weil scalar window and do not verify that half-plane claim. [C2, C3]

### 7. The 49 requirements and WP0–WP7

The complete crosswalk preserves each of the **49 original IDs**, its exact source paragraph, applicability and Round 2 destination. It is not a proof-of-discharge ledger. A successful route must complete the subgraph it uses; it need not solve every alternative. The historical 12 October “Track B” means first-negative-boundary propagation and maps mainly to today's C/D, not today's causal B. Both differ from the older CI Track A–D labels. [C2]

| Work package | Carry-forward disposition |
|---|---|
| WP0 | Refresh exact source and theorem authority; completed orientation is not restarted |
| WP1 | Reuse actual reciprocal-aperture concavity with its normalization and derivative premises when used |
| WP2 | Retain the K2 gap/gluing scope and explicit `hM51`; no all-cutoff or all-parity promotion |
| WP3 | Reuse strict-even adapters; keep odd/tie selected-ground requirements explicit |
| WP4 | **D2 Full remains deferred/open:** both K3 parity bottoms throughout \([1/512,\log16]\), with the small-aperture base below and every seam/normalization condition |
| WP5 | Preserve the originally prescribed modified-prime K2 crossing; later K3/Q14 or neutral controls do not silently replace it |
| WP6 | Preserve exact signed-correlation controls and the OPEN admissible signed upper |
| WP7 | Current integration, graph/registry and acceptance evidence remain separate from mathematical closure |

The archived guarded WP4 campaign has 30 verified layer payloads and 26 complete layers. The four unresolved even layers are Q9, Q13, Q14 and Q15, with 7, 7, 11 and 10 unresolved intervals respectively: **35 intervals total**. All 15 odd layers completed. The frozen SECOND feasibility check's 18/18 PASS is not this continuous full campaign. The FOURTH fallback applies after a frozen SECOND unresolved result, not as a tilewise substitution. `hWindows` remains an explicit premise, and no fresh full campaign was dispatched here. These retained engineering obligations do not block the independent finite filtered certificate. [C1, C3]

### 8. Implementation correction and validation

The standalone S06 four-column certificate depends on P04, S04 and S05 plus its finite periodic/Abel calculation. It does **not** require P19's general Gram chain. The unnecessary S06-to-P19 edge has been removed through an explicit revision record; P19 itself is unchanged. The exact finite baseline can therefore precede the general optimizer, inverse certificates and multi-zero machinery.

The proposed module manifest now covers every original contract, supporting amendment and optional extension. The core umbrella is separated from genuine optional classical imports; `ClassicalTransfer` may not be an axiomatic stub. The new modules for profiles, native cuts, synthetic controls, native jump controls, CT1 and finite neutral approximation are named rather than left implicit. The manifest is a proposed implementation plan, not a claim that those files already exist.

Validation checks the byte-for-byte preservation of the original contract array, deep equality of all inherited contract objects and metadata, unique IDs and names, source-reference resolution, alternative dependency groups, dependency acyclicity, module and milestone coverage, and false acceptance flags. The four terminal routes remain OPEN. Structural validation does not validate an analytic proof. The existing exact finite arithmetic scripts remain included and their unchanged receipts remain correctly identified.

The remaining mathematical work is still an independent source-specific estimate: a complete signed upper, an actual convergent raw or fixed-filter approximation, a source-matched Schur/energy upper, a valid positive-observation comparison, or an outgoing whole-kernel no-exit theorem. This audit makes those tasks and their prerequisites harder to omit; it does not supply the missing estimate.

### Sources and detailed ledgers

- **[C1]** `repo_omission_audit.md`, `repo_findings.json`, `repo_root_reuse_crosswalk.json`, `repo/current_workflow_harvest.json`, `repo/f5_aggregate_local_checks.json`, `repo/f5_dependency_delta_summary.json`, and `repo/historical_review_source_identity.json`. Current [PR294](https://github.com/HMarcusWH/zeta-23-lean/pull/294) and [pinned source tree](https://github.com/HMarcusWH/zeta-23-lean/tree/416aec21d4d6634675639b5397cc300d1f826e34).
- **[C2]** `project_omission_audit.md`, `project_findings.json`, and `project_requirements_49_crosswalk.json` / `.md`. Each source entry records the reviewed original path, hash, section and reading scope.
- **[C3]** `drive_omission_audit.md`, `drive_findings.json`, `drive_inventory_diff.json` and `drive_expanded_reading_ledger.json`; linked [Drive folder](https://drive.google.com/drive/folders/1FwRkN6sbJ4_Fhrqe53wpsJtByD2RXILb).
- **[C4]** [NearGapLimits.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/416aec21d4d6634675639b5397cc300d1f826e34/Zeta23/OPICAFollowup/NearGapLimits.lean), especially `dilation_normalized_limit_not_measure`, CT13Support and the controlled continuous-test extension.
- **[C5]** Original `RH_PoleNeutral_Contact_Investigation_2026-10-13.md` §§2.1–2.3, and current `CanonicalPoleNeutralCarrier.lean`, `CanonicalPoleNeutralPublicAPI.lean`, `BoundaryFlatApproximation.lean`, `NegativeWeilTestSupport.lean`, `FiniteNegativeObstruction.lean` and `BoundaryFlatFiniteWeil.lean`. Exact source locators and scaling caveats are in the project audit.
- **[C6]** Current [FiniteSpanSeparation.lean](https://github.com/HMarcusWH/zeta-23-lean/blob/416aec21d4d6634675639b5397cc300d1f826e34/Zeta23/OPICAFollowup/FiniteSpanSeparation.lean) and the repository's `DERIVED_FINITE_POSITIVE_TEST_OBSERVABILITY_2026-10-24.md`, copied with this package.
- **[C7]** Unchanged input `OPICA_Proof_Directed_Deep_Search_2026-10-25(2).md`, §§7.1–7.4.
- **[C8]** [PostGreen amendment v1.1](https://drive.google.com/file/d/1m2eHS65c7pH4aF8qSJe9s8FowyzZIr_D/view), read together with the current repository's [POST_GREEN_RESEARCH.md](https://github.com/HMarcusWH/zeta-23-lean/blob/416aec21d4d6634675639b5397cc300d1f826e34/research/RHRC/integration/opica_followup/POST_GREEN_RESEARCH.md), including the explicit epsilon=4 counterexample and corrected consumer scope.
