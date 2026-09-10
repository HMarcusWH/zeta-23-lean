# R003 — CCM / finite Weil bridge

Status: **ACTIVE. THEOREM AUTHORITY THROUGH PR #142. CURRENT FRONTIER = ANALYTIC FROZEN PREDECESSOR / DENSE FIXED-CELL REGULARITY, THEN REGULAR CANONICAL SCHUR-ENERGY SIGN. RH OPEN.**

## Current authority split

```text
live main after merged PR #142 = 3e8d2995a1c00a9aef0d8cb0f5382658c91a8673
live main tree = a92d03d0d4ad800d544a835b8ae2e3d23bae2c47

theorem-state anchor = PR #142 merge 3e8d2995a1c00a9aef0d8cb0f5382658c91a8673
validated theorem head = 23d96af9aafd86ad26ae7913c3d6c14503d539de
validated theorem tree = a92d03d0d4ad800d544a835b8ae2e3d23bae2c47
RHRC #889 = SUCCESS
Permansson #662 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

## Closed internal ladder

```text
F1 finite canonical obstruction                                  PROVED / #94
constrained / Euclidean finite wall                              PROVED / #96-#98
N-FLOW fixed-L negative tail                                     PROVED / #100
PARITY reversal / D-equivalence                                  PROVED / #102-#103
global first bad + nonnegative predecessors                      PROVED / #105,#112
negative mode + KKT + cubic channel                              PROVED / #107,#109,#110
V=W⊕S + shifted/zero-shift Schur package                         PROVED / #113-#128
source-explicit parity transfer                                  PROVED / #129
exact source-moment decomposition                                PROVED / #131
whole-kernel zero-shift source transport                         PROVED / #134
absolute canonical source energy                                 PROVED / #136
exact canonical source pairing                                   PROVED / #137
one-step determinant/channel formula                             PROVED / #137
domination -> zero-shift preimage + endpoint >=0                 PROVED / #137 CONDITIONAL
domination -> no safe negative explicit Schur root               PROVED / #137 CONDITIONAL
off-line zero -> q_c<0 OR exists Delta<0                        PROVED / #137
eventual negative witness at every sufficiently large aperture   PROVED / #140
eventual AnyParityBad + fresh global-first-bad selection         PROVED / #140
actual predecessor det!=0 <-> injective + unique preimage        PROVED / #140
frozen prime-cell equality + threshold zero + scalar -log split  PROVED / #140
actual canonical source continuity on a physical cutoff cell     PROVED / #142
fixed-vector canonical energy continuity on that cutoff cell     PROVED / #142
same-size/same-vector strict negative witness persistence        PROVED / #142
off-line zero -> locally persistent fixed witness                PROVED / #142
```

## Exact #136/#137 block objects

For the canonical one-step block:

```text
A = intrinsic predecessor block
c = intrinsic cubic shell
b = P_W T c
q_A(w) = Re<Aw,w>
q_c = Re<Tc,c>
Delta(w) = q_c*q_A(w) - |<w,b>|^2.
```

#136 provides scalar-sensitive self-energy and exact pole/arch/scalar/prime channel decomposition. #137 extends that bookkeeping to the exact complex pairing and determinant.

`canonicalOneStepDomination` is exactly

```text
q_c >= 0
AND
forall w, Delta(w) >= 0.
```

It is a proposition/certificate, not a proved property of the canonical source.

## A4R0 / A4R1a — what is now closed

**PROVED / #140:** a hypothetical off-line zero forces a finite negative canonical witness at every sufficiently large aperture, and the actual predecessor determinant/injectivity, unique-preimage, frozen-cutoff and scalar-log interfaces are theorem-locked.

**PROVED / #142:** on one physical cutoff cell

```text
I_Q = (log Q,log(Q+1))
```

with `Q>=1`, the actual production `canonicalSourceMatrix` is entrywise continuous and every fixed-vector real quadratic energy is continuous. A strict negative witness at one interior aperture therefore persists on an open `J subset I_Q` with the **same finite size and the same vector**.

The ExceptionalZero wrapper composes this with #140 beyond one aperture threshold.

Headline #142 declarations:

```text
continuousOn_canonicalSourceMatrix_apply_fixedCell
continuousOn_re_canonicalSourceQuadraticForm_fixedCell
exists_open_fixedCell_negativeCanonicalSourceWitness_persistence
eventually_fixedCell_negativeCanonicalSourceWitness_persists_of_offLine_zero
```

## Post-#142 route compression — cell-minimal size first

**DERIVED / PRIMARY DESIGN.**

Rather than obtaining an arbitrary witness size and regularizing a finite prefix, minimize bad size over the whole cutoff cell:

```text
K* = min { K | exists L in I_Q, AnyParityBad L K }.
```

Then:

```text
K*>=2;
size K* is bad at some L* in I_Q;
for every K<K* and every L in I_Q, neither parity is bad;
predecessor size N*=K*-1 is therefore PSD throughout I_Q.
```

Choose a bad parity witness at `(L*,K*)`. By #142 the same witness remains negative on an open `J subset I_Q`.

If the relevant predecessor determinant at size `N*` is nonzero on a dense subset of the cell, choose a regular aperture in `J`. The predecessor is then PSD by cell-minimality and injective by regularity, hence positive definite in finite Hermitian dimension.

For the bad parity's negative Schur-energy reduction, only that parity's predecessor needs regularizing. Regularizing both parities at the same predecessor size remains a useful stronger symmetric option.

A standalone abstract conditional theorem implementing the topological selection principle has been locally compiled. It assumes density and is **not merged theorem authority**.

## Current route — A4R1b analytic frozen predecessor regularity

**OPEN / PRIMARY REDUCTION TARGET.**

For fixed `Q,p,N`, construct an analytic family that is exactly the actual intrinsic predecessor on the physical cell.

Desired chain:

```text
complex continuation of the exact frozen production channels
-> actual frozen intrinsic predecessor
-> A(L) = -Log(L) I + B(L)
-> B single-valued holomorphic on a connected punctured domain
-> lift L=exp z
-> B(exp(z+2*pi*i))=B(exp z)
-> determinant nonidentity by finite-dimensional spectral/root counting
-> dense regular real apertures in I_Q.
```

The #140 theorem already validates the scalar real-axis `-log L` contribution. The unresolved work is the full production remainder and its exact compression.

## Direct archimedean analytic lead after #142

#142 regularizes the apparent origin singularity in the real production archimedean integrands using divided slopes of `sinh`, `cos`, `exp` and `Real.sinc`.

After the real substitution `x=L t`, the interval is fixed at `[0,1]` and the oscillatory frequency is independent of aperture. Schematically:

```text
alpha_n(L) = 2*n * integral_0^1 sinc(2*pi*n*t) * h(L*t) dt
beta_n(L)  =       integral_0^1 cos(2*pi*n*t)  * h(L*t) dt
```

with an analogous divided-slope expression for `sourceEq44GammaL-wCorrection`.

These rescaled identities are **DERIVED**, not merged Lean declarations. Their high-precision comparisons are **EXPERIMENTAL SIGNAL**, not proof.

This representation makes direct parameter holomorphy a plausible primary route. `DictionaryArchPhysical.lean`, `DictionaryArchBridge.lean` and `GammaFacts/Mu.lean` remain resurrected fallback/cross-check infrastructure.

## Candidate determinant-nonidentity mechanism

The correct monodromy architecture is not an unsupported statement that the physical family is periodic. It is:

```text
A(L) = -Log(L) I + B(L)
```

where `B` is single-valued in the aperture variable on a punctured domain. With `L=exp z`:

```text
Ahat(z) = -z I + B(exp z)
B(exp(z+2*pi*i)) = B(exp z).
```

If `det Ahat` vanished identically, the same finite matrix `B(exp z0)` would be forced to admit more distinct eigenvalues `z0+2*pi*i*k` than its dimension allows.

This is a **LEAD / HYPOTHESIS** until the full continuation, branch/domain and actual predecessor equality are theoremized.

## Next route — regular canonical Schur-energy sign

If analytic regularity succeeds, compose dense regularity with the cell-minimal bad state and #142 persistent-negative open set.

At the selected state:

```text
A>=0                    from cell/global minimality
A injective             from regularity
A>0                     finite Hermitian consequence
unique x0 with A x0=b   #140 scaffold
u0=c-x0.
```

Use the unique-preimage interface in Lean rather than making inverse notation load-bearing.

The intended packaged forced countercertificate is

```text
Ecanonical(u0) = Re S0 < 0.
```

The decisive arithmetic target becomes

```text
Ecanonical(c-x0) >= 0
```

on that exact forced regular trial, equivalently in inverse shorthand

```text
<b,A^-1b> <= q_c.
```

This theorem must use exact canonical pole/arch/scalar/prime interaction. An auxiliary positive form whose positivity is equivalent to successor PSD is circular.

## Stronger post-#142 falsification

A generic analytic centered diagonal family now serves as a negative control. It simultaneously has:

```text
analytic positive-aperture dependence;
explicit -log L scalar term;
positive predecessors for every L>0;
persistent finite negative witnesses at every aperture;
a globally minimal bad size;
common negative behavior in both parities.
```

It is not the canonical zeta source. It proves only that persistence + cell/global minimality + regularity + parity + scalar logarithmic structure are insufficient for the contradiction.

See `../../countermodels/POST_142_REGULARIZATION_COUNTERMODEL_2026_09_10.md`.

Regularity also makes the relevant predecessor kernel trivial, so the #134 `Gamma0*mu(z)=0` product law does not by itself become a sign theorem on the selected regular state.

## Universal domination fallback

Universal `q_c>=0` and `Delta(w)>=0` for every predecessor direction remains a valid closing theorem. It is deferred rather than killed. Promote it again only if a genuinely independent positive canonical source representation or exact arithmetic remainder is found.

## Permanent normalization / claim firewalls

- canonical sign-sensitive object is `canonicalSourceMatrix` under the repaired source convention;
- legacy `finiteMatrix` cannot supply absolute sign automatically;
- theorem authority is through #142;
- aperture freedom, fixed-cell continuity and same-witness persistence are PROVED;
- analytic frozen predecessor / determinant nonidentity / dense regularity are OPEN;
- cell-minimal regular selection is DERIVED until production-packaged;
- regular canonical Schur-energy nonnegativity is OPEN;
- regularity alone does not exclude a negative successor;
- no all-size Baire or finite-prefix regularization is required unless the smaller cell-minimal route fails for a theoremized reason;
- no inverse is load-bearing before regularity; prefer unique preimage;
- no division by unproved transfer factors;
- D is algebraic, not unitary/isometric;
- generic/modified-source countermodels do not refute canonical CCM;
- numerical precision is not theorem authority;
- RH remains OPEN.

Detailed current implications: `../../RESEARCH_LEADS_POST_142_FIXED_CELL_PERSISTENCE_DELTA.md`.

**RH remains OPEN.**