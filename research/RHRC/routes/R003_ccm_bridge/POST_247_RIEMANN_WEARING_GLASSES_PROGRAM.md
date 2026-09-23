# Post-#247 programme — It's Riemann Wearing Glasses All the Way Down

Status: ACTIVE RESEARCH PROGRAMME after merged PR #247.

The title is intentionally informal. The mathematical content below is not.

Claim firewall: RH remains OPEN.

## 1. Executive statement

The repo now has several exact representations of the same canonical finite Weil object. The research opportunity is not that equivalent representations create new information. They do not.

The opportunity is that different coordinates expose different structures:
- a spectral minimum in one chart;
- codimension and interlacing in another;
- von Mangoldt threshold updates in another;
- source moments/test weights in another;
- Schur/secular contact geometry only in the bad region.

Glasses v2 uses each chart only on its valid domain and attacks the first possible transition from nonnegative to negative canonical ground energy.

## 2. Exact post-#247 authority

PR #247:
- head 7438f2a23750b1f4133c12b989eb9d81c1e99eea
- merge 070c0a08a924d0c917d5366755f9c4d50067ce51
- tree 1672e49e092682343a2eace1e8e6e4799c102f35
- 11/11 attached workflows completed successfully

PR #246:
- head 77e22249a1fca5701ae6e52ed9cc84cd0a819e26
- merge dad3ecb145fe92e84ff4ff630eab4d5847c65f77
- tree 5c78df3525b6e87514f5aa3b888f4849d53aa99c

RH remains OPEN.

## 3. Current theorem-backed chain

    off-line zero
      -> arbitrarily-large whole-cell bi-regular retained negative states        (#243)
      -> terminal gates shown RH-equivalent                                    (#245)
      -> canonical weighted-von-Mangoldt remainder normal form                  (#246)
      -> universal finite-Weil/Riesz/prime-dominance criteria shown RH-equivalent (#246)
      -> unconditional parity Rayleigh/global-bottom spectrum                   (#247)
      -> GlobalBottomResidualState + dependent branch package                   (#247)
      -> same true residual-state ground eigenmode                              (#247)
      -> negative canonical channel energy on that ground trial                 (#247)
      -> same-witness #246 prime-remainder failure                              (#247)
      -> exact continuous primeTestWeight / weighted remainder integral          (#247)
      -> arbitrarily-large GlobalBottomArithmeticResidual                       (#247)
      -> OPEN unconditional new arithmetic/spectral mechanism
      -> only then could residual states be excluded
      -> terminal Mathlib RH seam already available                             (#242)

## 4. The central correction to the original Glasses draft

PR #247 proves:
GlobalBottomResidualExclusion <-> RiemannHypothesis.

Therefore a law C stated only on residual states cannot be advertised as "strictly weaker than RH" if:
- every residual state violates C; and
- the proposed theorem is "every residual state satisfies C."

That universal theorem is just residual-state nonexistence and hence RH-equivalent.

This is the **Residual-state vacuity firewall**.

The repair is to formulate candidate laws on objects that exist unconditionally for every legal aperture/size.

## 5. Unconditional canonical objects

The repo already supplies the key starting point:
- parityRayleighBottom p L K;
- globalParitySuccessorBottom L N;
- bottom attainment in successor parity spaces;
- exact finite canonical Hermitian/symmetric operators;
- exact boundary-flat and parity carrier geometry.

The first new interface should package the unconditional minimum and ground eigenspace without assuming negativity.

Do not define a globally canonical u_star unless simplicity is separately proved. If the bottom eigenvalue has multiplicity, use the eigenspace or quantify over normalized bottom eigenvectors.

## 6. Domain atlas

| View | Domain | What it exposes | Must not be inferred |
|---|---|---|---|
| canonicalSourceMatrix | unconditional | exact finite operator | positivity |
| full finite Fourier carrier | unconditional | published/source spectral comparison | legality for zeta Weil tests |
| boundary-flat carrier | unconditional | legal C2 zeta Weil tests; codimension three | same ground vector as full carrier |
| even/odd boundary-flat carriers | unconditional | parity minima and exact dimensions | equal spectra |
| parityRayleighBottom/global bottom | unconditional | spectral minimum | unique minimizer |
| fixed-cell energy/matrix continuity | unconditional on a cell | local L evolution | global monotonicity |
| #246 prime-remainder normal form | unconditional | exact arithmetic decomposition | dominance |
| GlobalBottomResidualState | requires badness | aligned negative state | existence under RH |
| #247 groundTrial/branch package | residual-state chart | true bad ground geometry | unconditional ground-vector law |
| safe negative-shift secular chart | lambda < 0 plus regularity | resolvent/secular transfer | behavior at zero without a limit/contact theorem |
| audit equivalence modules | audit-only | anti-circularity | active proof step |

## 7. Carrier glasses

For N >= 1 the full centered Fourier coefficient space has dimension 2N+1.

The boundary-flat carrier imposes exactly three independent centered moments:
m0 = m1 = m2 = 0,
and has exact dimension 2N-2.

It then splits into exact even/odd boundary-flat parity sectors.

This yields a natural spectral ladder:

    full finite carrier
        |
        | codimension 3 restriction
        v
    boundary-flat carrier
       / \
      /   \
    even  odd

The next formal goal is a min-max/interlacing atlas across these carriers.

This is structurally different from ordinary Gram positivity: it compares different constrained spectra of the same canonical operator.

## 8. N glasses

NestedFinite and parity geometry already prove exact centered zero extension:
- preserves centered modes;
- preserves moments/boundary-flat membership;
- preserves parity;
- preserves Euclidean norm;
- preserves the localized finite function;
- preserves the canonical quadratic value.

DERIVED / NOT YET SEPARATELY FORMALIZED:
for M >= N, the parity-restricted Rayleigh bottom at size M should be <= the corresponding bottom at size N.

This theorem is cheap, unconditional, and should be built early.

Interpretation: adding Fourier directions cannot rescue a negative minimum. N-flow is useful for persistence/onset geometry, not positivity induction.

## 9. L glasses

The canonical matrix/energies are continuous on a fixed physical cutoff cell.

Inside a cell:
- use analytic/spectral coordinates;
- use Hellmann-Feynman only when the relevant eigenvalue is simple;
- otherwise use multiplicity-safe min-max, one-sided derivatives, or spectral-projector statements.

At L = log(p^k):
- switch to arithmetic/source coordinates;
- isolate the exact von Mangoldt seam/update;
- keep the canonical normalization fixed.

The goal is not lambda_min'(L) >= 0 globally.

The goal is to prevent the **first crossing through zero**.

## 10. Threshold-local first crossing

Target architecture:

1. prove an unconditional nonnegative base region;
2. suppose L_star is the first aperture where the ground bottom reaches zero;
3. use fixed-cell/contact structure on the side from which L_star is approached;
4. use the exact prime-power update if L_star is a seam;
5. prove that neither an interior contact nor an arithmetic seam can cross into negative energy;
6. conclude no first crossing exists.

DR-021/DR-022 do not kill this architecture because they killed global fixed-sign derivative claims, not local contact plus seam analysis.

## 11. Arithmetic glasses

PR #246 gives the exact arithmetic decomposition:
canonicalSourceChannelEnergy
  = -canonicalPrimeRemainderEnergy
    - canonicalPrimeFreeBudget.

PR #247 further proves that, on a hypothetical bad global ground state, the same true ground trial yields the exact primeTestWeight and the exact failed dominance inequality.

The next useful question is not "can we prove dominance for all residual states?"

It is:
what unconditional restrictions does the ground eigenspace impose on the admissible prime-test weights before badness is assumed?

Candidate restrictions:
- boundary moments;
- endpoint jets;
- parity symmetry;
- normalization-invariant moments;
- support/regularity;
- low-rank carrier relations;
- threshold update identities.

Every candidate must pass the vacuity firewall and control tests.

## 12. Source/prolate glasses

R004 contains two historically distinct ideas.

Still dead:
- fitted small-commutator -> eigenvector convergence without a uniform spectral gap.

Resurrected:
- exact source-coordinate/kappa map;
- canonical source normalization;
- analytic/full-space prolate spectral structure;
- external QW_lambda / kappa / PsiSharp correspondence as a source bridge.

The repository already proves the genuine zeta Weil form equals canonicalSourceMatrix on legal boundary-flat finite vectors. The remaining external source bridge is useful for importing published full-space spectral structure, not for re-proving that internal finite identity.

No published lowest full-space vector may be identified with the boundary-flat/parity ground vector without an exact theorem.

## 13. Countermodel hierarchy

### Pair-D
Role: generic finite-dimensional falsifier.
Question: is the proposed law just Hermitian/parity/shell/displacement algebra?

Passing Pair-D is necessary but not sufficient for zeta-specificity.

### Planted off-line canonical-style control
Role: primary next falsifier to build.
Requirements:
- explicit fake zero data;
- explicit resulting arithmetic/explicit-formula data;
- declaration of which canonical relations are preserved;
- declaration of which zeta/Euler-product facts are broken;
- no arbitrary "edit R(x)" shortcut presented as a genuine zeta model.

Question: does the candidate unconditional law hold on real canonical data but fail in a controlled off-line world for a specifically identified arithmetic reason?

### External zeta-adjacent controls
Use only as research falsifiers, with source/normalization caveats.

## 14. What is dropped

Dropped from active theorem work:
- nonzero holonomy around exact equality cycles;
- ordinary Hilbert-space Gram PSD as an RH sign source;
- compatibility among conditional bad-state charts as if compatibility itself created new information.

## 15. What is parked

Relation-zeta is PARKED / SPECULATIVE.

Revisit only if:
- the graph/dynamics is canonical and mathematics-generated;
- primitive cycles are invariant under proof refactoring;
- no fitted weights/order are used;
- negative controls are specified in advance;
- a theorem connects the graph operator to the canonical Weil/arithmetic object.

A graph of "lemmas we happened to write" is not a canonical RH object.

## 16. Anti-numerology firewall

Any discovery experiment must predeclare:
- exact inputs;
- exact candidate observable;
- control models;
- success/failure threshold;
- normalization;
- whether the result is theorem, derived consequence, experimental signal, or hypothesis.

No fit-to-zeta cycle weights, no post-hoc feature selection presented as a theorem route, and no terminal claim promotion from numerical agreement.

## 17. Execution plan

### Work package A — post-#247 state sync
Documentation/machine-state only. Freeze #246/#247 authority and Glasses v2.

### Work package B — unconditional ground-spectrum atlas
Create theorem-facing interfaces for:
- bottom values;
- bottom eigenspaces/minimizers;
- carrier inclusions;
- parity minima;
- same normalization across all charts.

### Work package C — N-flow
Formalize parity-bottom monotonicity under centered zero extension.

### Work package D — carrier min-max
Full -> boundary-flat -> parity spectral bounds/interlacing.

### Work package E — unconditional prime-test weight
Lift the useful #247 weight formulas away from residual-only hypotheses.

### Work package F — fixed-cell L dynamics
Multiplicity-safe spectral variation inside one physical cutoff cell.

### Work package G — prime-power seam
Exact constrained-operator/energy update at L = log(p^k).

### Work package H — positive base
Prove a real base theorem. Do not substitute "no primes yet" for positivity.

### Work package I — first-crossing barrier
Compose F+G+H.

### Work package J — terminal composition
Only after I is premise-free: exclude residual states and use the already-proved RH seam.

## 18. Success criteria

A candidate law C advances the project only if:
1. C is defined on unconditional objects or its conditional domain is explicitly justified;
2. C is nonvacuous when RH is true;
3. C is not merely a renamed already-proved RH-equivalent terminal gate;
4. C has a theorem-backed arithmetic/analytic source;
5. C survives Pair-D if it claims zeta-specific content;
6. a planted off-line control provides a meaningful falsification target;
7. normalization and carrier semantics are exact;
8. any eigenvector selection handles multiplicity honestly.

## 19. Fastest ways this programme could fail

- the full/boundary-flat carrier relation gives only generic interlacing with no useful arithmetic consequence;
- unconditional ground prime weights have no extra constraints beyond boundary flatness;
- the base positivity theorem is as hard as RH itself;
- the first crossing can happen inside a cell and local contact calculus provides no source-specific restriction;
- the prime-power seam is too weak to compensate for background drift;
- the prolate/full-space structure disappears under the codimension-three constraint;
- planted off-line controls satisfy every proposed local law.

These are useful failures: each removes a family of routes.

## 20. Highest-leverage immediate theorem PR after the sync

The first mathematical PR should be deliberately modest:

**Unconditional Ground Spectrum Atlas + N-flow Monotonicity**

It should not attempt RH.

Expected contents:
- a canonical ground-value/eigenspace/minimizer interface;
- no global choice of eigenvector;
- exact carrier inclusion lemmas;
- parity-bottom monotonicity in N;
- machine-readable claim bindings;
- no new terminal equivalence.

That PR will tell us whether Glasses v2 has a clean unconditional spine before we invest in threshold dynamics.

## 21. Standing questions

What becomes possible now that the #247 bad-state package is attached to the true global ground trial?

Which relations are genuinely new constraints and which are only definitions of the same two-parameter family?

What exact property of the classical von Mangoldt seam is absent from planted off-line controls?

Can the full-space prolate spectral structure survive the exact three boundary moments?

Can a multiplicity-safe first-contact theorem be made strong enough to compose with a prime-power update?

What is the smallest theorem that would falsify the Glasses v2 programme quickly if the route is illusory?

RH remains OPEN.
