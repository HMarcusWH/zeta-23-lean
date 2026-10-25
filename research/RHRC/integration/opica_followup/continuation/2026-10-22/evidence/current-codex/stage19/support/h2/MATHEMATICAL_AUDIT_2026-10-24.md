# OPICA H2 and native-rate mathematical audit — 24 October 2026

Base repository HEAD: `cea7b2f62ea847c18958cc7385151c8c2b09520d`.
Committed tree: `377c7f6f36375a4ac35d3f3ad17ee95b340eb9eb`.
The later boundary countercontrol compiled after the parent's source commit
`59ff485551771c0ab6322562d18fb8e9d4166da4`, tree
`396665de3d14c2db60a4a85c646dd56d718f07ff`. The receipt records each
individual compile's repository context; its resumed prefix was not
mislabelled as a fresh rebuild at the later head. Relevant imported source
hashes are unchanged.
This audit was conducted in `work/audit-math`, outside production sources. The
parent agent owns the production Consumers change and broad dependency builds.
No H2a/H2b/J5.2/MS1 original root is promoted by this audit. RH and Step 4 remain OPEN.

## Controlling contracts inspected

- Root `AGENTS.md`, continuation `README.md`, `STAGE18_HANDOVER.md`,
  `ROOT_LEDGER_100.json` and `REMAINING_WORK.md`.
- Frozen `research/RHRC/integration/opica_followup/BUILD_SPEC.md`: H2a/H2b
  families at lines 552–574; exact root clauses at lines 1280–1290 and
  1436–1458; actual-force consumer at lines 1600–1606.
- `paper/OPICA_Followup_Final_Audited_Paper_2026-10-21.md`: A1–A8 at
  lines 90–275, H1/H2 at lines 1872–1963.
- Actual definitions/proofs in `CoPoissonJets.lean`, `MultiplicityTail.lean`,
  `UniformSourceBounds.lean`, `AuxiliaryCompletions.lean`,
  `NativeWindowRate.lean`, `ComplexLocalMeasures.lean`, and the parent's
  `OPICA/SignedHeatSeparator.lean`.

The baseline has no ConfluentProfiles, FiniteSpanSeparation or
MovingSourceWindowRate module. NativeWindowRate has physical definitions and
elementary support only. The ledger's 90-root figure combines historical and
narrow evidence; it is not a current all-100 aggregate receipt.

## Exact determinant and falsification

H2a's matrix is

`A[n,(j,k)] = (1/k!) d^k/dκ^k [κ (1/4−κ)^n] evaluated at κ_j`,

with `0 ≤ n < M`, `0 ≤ k < m_j`, total `M = Σ m_j`, and column order
`(j,0),(j,1),…`. It is the matrix of odd Taylor derivatives of the weighted
first-cell density; the `(2n+1)!` is removed by taking that odd derivative.

The required determinant is exactly

`(−1)^(M(M−1)/2) ∏ κ_j^m_j ∏_(i<j) (κ_j−κ_i)^(m_i*m_j)`.

`check_confluent_controls.py` and `confluent-controls.json` pass 17 exact
SymPy 1.14.0 systems: empty dimension, multiplicities 1–4, multiple nodes,
κ=1/4, complex conjugate nodes, zero nodes and repeated nodes.
These are finite algebraic controls, not a universal proof or actual-zero experiment.

- Two simple nodes: determinant `a*b*(a−b)`, checking the global sign.
- One node κ=2 of multiplicity three: normalized determinant −8; raw
  derivative determinant −16. Forgetting normalization introduces the
  product of local derivative factorials.
- Coalescence at nodes 1 and 1+ε: determinant `−ε(1+ε)` tends to zero.
  Thus finite invertibility cannot supply a uniform inverse constant under
  collisions. Increasing multiplicity jets describe the limit but do not
  remove conditioning costs from a changing ordinary basis.
- κ=0 or reflection-duplicate nodes make the prescribed determinant zero.
  Reflection must be removed before independence is asserted.
- κ=1/4 introduces no algebraic singularity: the entire Sh series removes
  a square-root-branch issue. Actual zeta zeros do not equal 1/2; that
  separate analytic fact is supplied upstream.

## Verified scratch Lean support

`NormalizedJetBlock.lean` defines normalized coordinate multiplication on
jets as `κ*a_k + [k>0]*a_(k−1)`. It proves that this truncated map is
injective for κ≠0, with no derivative factorial on the predecessor term.
`ExpectedNormalizedJetBlock.lean` independently states its kernel and
injectivity types. `NegativeZeroNode.lean` fails as intended when κ≠0 is
deleted. The source, consumer, negative-control logs and exit codes are in
`normalized-jet-receipt.json`.

- Compiler: Lean 4.33.0-rc2, Windows x86_64, commit
  `d8b18978322de05a8f3dba51ef03cf5461676c17`.
- Direct compiler commands and exact source/log SHA-256 values are in that
  receipt. Outputs are isolated in this scratch directory.
- Source and expected consumer both exit 0. Negative zero-node control
  exits 1 at the attempted proof of `0 ≠ 0`.
- Every printed axiom closure is exactly a subset of
  `{propext, Classical.choice, Quot.sound}`; no sorryAx or project axiom.
- Source SHA-256:
  `d2fe82d88a16e1d7f6dae948de193792d59065c2a56f0674abd359fa8bfc475e`.

The complete additional support gate is sealed in
`confluent-algebra-receipt.json`: nine positive source/consumer compiles
exit 0 and two deliberately false controls exit 1 at their intended
arithmetic `False` goals. All accepted printed axiom closures are
standard-only. Exact source/log hashes and command arguments are recorded,
with the base HEAD/tree and actual CoPoissonJets/ZeroProfiles/toolchain/
manifest source hashes. Earlier failed elaboration logs and partial
receipts are preserved separately.

- `ConfluentAlgebra.lean`: polynomial functional-matrix factorization,
  monic-basis determinant invariance, Newton monicity/degree.
- `NewtonHermite.lean`: exact general normalized Hermite determinant for
  arbitrary expanded node sequences, over nontrivial commutative rings.
- `CoordinateConfluent.lean`: the additional product of nonzero nodes.
- `AffineConfluent.lean`: the complete expanded-node polynomial determinant,
  including the affine basis and exact global sign. Its successful proof
  uses the repository's 800000-heartbeat cap; the earlier 200000-heartbeat
  failure is retained as failed evidence.
- `ExpectedConfluentAlgebra.lean`: independently written inline matrix
  expected types and exact zero-node, duplicate-block, sign and factorial
  controls. NegativeConfluentSign/Factorial reject the wrong formulas.
- `HasseNormalizedDerivative.lean`: Hasse evaluation is exactly analytic
  iteratedDeriv divided by k! over characteristic-zero nontrivially normed
  fields. This generic polynomial normalization bridge is PROVED.
- `ActualFirstCell.lean`: the actual existing zeroFamilyDensity on [1,2),
  its weighted log-cell identity and every normalized κ-jet identity.
- `ExpectedActualFirstCell.lean`: actual-definition/full expected type,
  the endpoint density, the left gap and the exact κ=1/4 right-cell formula.
- `PhysicalBoundaryCountercontrol.lean`: the real part of the actual
  κ=1/4 physical weighted density is not differentiable at u=0. The proof
  reduces it locally to absolute value. This exact boundary falsification
  is PROVED, not a numerical signal.

These are supporting results, not the original H2a roots or a full100
compiler receipt. The physical odd-u coefficient bridge and original
grouped multiplicity-index construction remain OPEN.

## Full determinant route

Use an expanded node sequence `node : Fin M → K`; the jet order at column
`j` is the number of previous occurrences of `node j`. Define the monic
Newton polynomial `P_i = ∏_(l<i) (X−node_l)`.

1. A monic degree-i basis has determinant-one coefficient matrix, so it
   preserves every polynomial linear-functional determinant.
2. Taylor-expand P_i at node_j. It is `X^r` times the product of
   `(X+node_j−node_l)` over previous unequal nodes, where r counts previous
   equal nodes before i.
3. For j<i this r exceeds the jet order at j, so the Hermite matrix is
   upper triangular. Its diagonal is the product of earlier unequal gaps.
4. Therefore the normalized Hermite determinant is the product of all
   unequal prior gaps. This statement works over any nontrivial commutative
   ring, without distinctness assumptions or analytic limits.
5. For the extra factor κ, prepend node 0 once and expand the larger
   monomial Hermite determinant along its first column `(1,0,…,0)`.
   Nonzero original nodes preserve their original jet orders; the new gaps
   contribute exactly `∏ node_i`.
6. The affine basis `(1/4−X)^n` has triangular coefficient matrix with
   diagonal `(−1)^n`, yielding the required sign.
7. A final grouped-node reindexing converts the expanded gap product to
   exponents `m_i*m_j`, and `∏ node_i` to `∏ κ_j^m_j`.

The occurrence convention must not hide duplicate original blocks. The
sequence `[κ,κ,κ]` in the generic theorem denotes derivatives 0,1,2 of one
node. Two supplied original blocks at the same κ would each restart their
derivative index at zero and have duplicate columns instead. Their negative
control determinant is zero. The grouped bridge must use the required
distinctSpectralNodes hypothesis and the prescribed multiplicity bounds;
it cannot merge reflected zeros and thereby invent additional admissible jets.

The final grouped reindexing and the odd-u coefficient identification for
the actual right-cell continuation remain necessary before declaring the
original determinant root complete. The generic Hasse-to-normalized-
iteratedDeriv identification is now proved separately. Actual-measure
independence additionally needs the measure-to-first-cell-density and
analytic identity argument; an algebraic matrix theorem alone does not
supply it.

**Boundary-domain falsification:** do not define this matrix using ordinary
two-sided derivatives at u=0 of the global physical function
`exp(u/2)*zeroJetDensity κ k (exp u)`. That function is zero for u<0, whereas
its k=0 right-cell expression begins κu and its k=1 expression begins u.
Thus it has the expected first-cell derivative jump. The paper takes Taylor
coefficients of the analytic RIGHT-CELL CONTINUATION
`(1/k!) d_κ^k [κ Sh(1/4−κ,u)]`, whose equality to the physical density is
restricted to `0≤u<log 2`. The next bridge must explicitly use this
continuation or justified right derivatives. A two-sided global derivative
matrix would be a false physical identification, not a harmless notational
change.

An exact elementary countercontrol is κ=1/4: Sh(0,u)=u, so the weighted
physical density is u/4 for `0≤u<log 2` and zero for u<0. Its left slope is
zero and its right slope is 1/4. This is the actual construction at a test
parameter, not an assertion that κ=1/4 comes from a zeta zero. More
generally the k=0 right slope is κ;
for k=1 the right slope is one while the left slope remains zero. The
quarter-parameter non-differentiability is now formally proved in the
countercontrol source above. The general slope interpretation here is a
DERIVED consequence of the right-cell series, not an additional exported
Lean theorem. The
correct independence route is measure equality → density zero on (1,2) →
analytic right-cell continuation zero on an open interval → all Taylor
coefficients zero → the Hermite system. No global derivative at the
boundary is needed.

The next minimal analytic statement (OPEN here) can be stated without any
zero premise. For
`F_(κ,k)(u) = iteratedDeriv k (fun w : ℂ => w*shKernel(1/4−w,u)) κ / k!`,
prove

`iteratedDeriv (2*n+1) F_(κ,k) 0 =
 iteratedDeriv k (fun w : ℂ => w*(1/4−w)^n) κ / k!`.

The outside derivative is in the real u coordinate; the inside derivative
is complex in κ. A joint entire extension in complex u, proved from the
normally convergent Sh series, would justify coefficient extraction and
the mixed derivatives. The available first-cell equality is not itself a
proof of this interchange.

## Finite-span separation: smaller route and non-vacuity

The parent signed sharp-gap separator already returns vanishing of both
canonical Jordan measures. LocallyFiniteSignedMeasure includes mutual
singularity, so there is no noncanonical common-positive-mass ambiguity.
ComplexLocalMeasures has actual canonical addition/scaling adapters with
compact-restriction linearity; it is not yet a scalar-module API.

For a real basis built from H1 jets, avoid proving continuity of Jordan
decomposition directly. Write its actual signed measure as
`ν_a = f_a dx − A_a comb_nonzero`. The sinc-squared weight s vanishes on
the lattice. The exact separator pairing gives `∫s dν_a = 0`, hence

`negative_weighted_mass(ν_a) = (1/2) ∫ s(x)|f_a(x)| dx`.

This identifies the budget with half the L1 norm of the linear map
`a ↦ s*f_a`. Injectivity follows from the separator and H2a; finite-dimensional
norm equivalence then gives `c_basis > 0`. This is DERIVED mathematics,
not separately formalized here. Handle the zero-dimensional coefficient
space separately, where any positive constant works.

Realification must retain the actual conjugacy relation. For nonreal κ,
`a Re ν + b Im ν = (a−ib)ν/2 + (a+ib)conj(ν)/2`. For real κ (critical-line
zeros), the density and measure jets are real; their imaginary parts are
zero and must not be included as independent real basis vectors. Reflection
duplicates are not additional nodes.

This proves a genuine obstruction to every finite linear repair from these
actual jets, including multiplicities. It does not exclude off-line zeros,
nonlinear constructions or uncontrolled infinite limits. The determinant
depends on the zero equation only through the existence of admissible H1
jets; the first-cell algebra itself works at arbitrary nonzero nodes,
including nonreal ones. Therefore the determinant and independence mechanism
cannot by themselves force κ to be real or exclude a hypothetical off-line
zero. The source-specific signed separator composition supplies the finite
repair restriction; an independent opposing bound remains OPEN.

## J5.2/MS1 uniformity audit

No quantifier defect or circular analytic premise was found in A1–A8.
An initial suspicion about a pointwise/eventual mismatch was rejected after
reading the full proof: A6 is valid for every completion index, source order
and real horizon; its constants are selected before specializing to k(T).

- `source_order_uniform_norms`: one positive C before every source order d.
- `native_field_theta_envelope`: one positive C before every d, with the
  actual zero-displacement supremum and literal source-dependent constant.
- `aux_completion_ratio_bounds`: one Cp for a selected actual right zero,
  before every completion index k≥1.
- `native_terminal_memory_lower`: exact positive-part A6 for all k,d,T,
  using finite prime histories and stable completed inputs, without global
  prime-field L2 membership.
- `nativeMultiplicityTailConstant_pos`: actual zero multiplicity and
  source visibility prove positivity rather than assume it.

The missing proof composition must establish:

1. For any b<Theta choose one actual right zero with
   `delta > (Theta+(C−1)b)/C`; no attained supremum is required.
2. Choose ξ in `((Theta−delta)/(C−1), delta−b)`. The existing elementary
   parameter lemmas prove the strict exponent separations. Since
   delta≤Theta, ξ is positive.
3. Prove real-horizon floor asymptotics for
   `k(T)=max(1,floor(ξ*T/log T))`: k→∞, k/T→0,
   `k log T/T→ξ`, and `k log(k+1)/T→ξ`.
4. Price both signs of `log|J_d(p)|`, not just its upper side, from
   `J_d(p)=(p²−1/4)^d J_0(p)`. For fixed p this cost is O_p(d+1).
5. Under `d log(d+2)=o(T)`, obtain the `(d+1)log(d+2)=o(T)` source cost
   required by the actual uniform norm/envelope theorems. The finite d=0
   prefix is harmless but should be discharged explicitly.
6. Use the L1-filter/source norm bound to make the subtraction in A6
   negligible relative to its positive witness, then take the lower
   logarithmic rate. No cancellation of an uncontrolled signed difference.
7. Split memory at `T−C log T`. Bound its early part by
   `C_d/(alpha+Theta) exp(Theta*T−(alpha+Theta)C log T)` and compare its
   strict upper exponent `Theta−Cξ` to the witness `delta−ξ`.
8. Apply Cauchy–Schwarz to the remaining actual continuous window and its
   exact exponential weight. Prove the matching upper bound directly from
   the source envelope. For Theta=0, use nonnegativity of log(1+energy).
9. Derive the continuous fixed-source theorem, then MS1 along arbitrary
   positive-eventually real cofinal schedules with source order growth.

Numerical floor controls in confluent-controls.json are sanity checks only.
Convergence of `k log(k+1)/T` is noticeably slow and cannot be replaced by a
finite numeric tolerance. No sample computation establishes J5.2/MS1.

## Independent semantic review of the installed force/sampling consumer

The current candidate and ExpectedForceSampling meet the original
BUILD_SPEC consumer clause at the semantic level. They explicitly retain:
the actual lattice force on compact log tests; both Fourier conventions;
the actual log-unitary zero profile and weak forced equation; arithmetic
zeta spectral density divided by 2π; sample identity b=κM(κ); generic
boundary coefficient ζ/b; and the right-half-strip representative chosen
from the original zero or its reflection with the same κ.

The nonreal-κ premise is the intended F2 domain. No nonreal zero is asserted
to exist; hypothetical off-line usage is deliberately conditional. No
spectral-domain, reality, positivity or homogeneous-operator conclusion is
assumed. A homogeneous Euler-image negative control and replay of the old
word/jet consumer remain appropriate. This audit is semantic review;
compiler validity is owned by the parent's exact-source gate.

## Post-Green Research Pass for the scratch support

- **Formally true:** the local normalized κ-jet multiplication kernel and
  injectivity results, independent expected types, and the monic polynomial
  functional-matrix factorization/degree results, on their exact compiled
  sources. These are supporting theorems only.
- **Workflow harvest:** no GitHub job was changed or harvested by this
  subtask. Its local compile/expected/negative dispositions are separately
  source pinned. No full-release implication follows.
- **What changed:** the determinant route can proceed without complex
  differentiation of a determinant or limits of colliding nodes. Hasse jets
  and Newton polynomials express it algebraically.
- **Upstream:** normalized jets are naturally Hasse/Taylor coefficients;
  that formulation explains the missing factorial negative control and
  compresses the local κ-multiplication step.
- **Downstream:** once the full determinant and analytic first-cell bridge
  compile, actual independence feeds the P0 separator and fixed-basis norm
  equivalence. The finite-span negative mass is a weighted L1 norm.
- **Resurrected routes:** a generic polynomial Newton/Hermite determinant
  route is feasible; no prior impossible RH route has been revived.
- **New RH-relevant clues:** finite-span exclusion can be quantitative on
  each fixed basis. Uniform moving-basis coercivity remains OPEN.
  First-cell determinant invertibility cannot establish it because the
  explicit determinant degenerates under coalescence. This is a limitation
  of that inference, not a proof that every possible global weighted-mass
  lower bound fails for actual zeros. Additional global information would
  be needed in an infinite limiting argument.
- **Falsification:** signs, factorials, empty systems, zero nodes, repeated
  nodes, complex conjugacy, critical κ and coalescence have been tested.
  Actual off-line-zero existence and analytic independence were not tested
  by those finite controls.
- **Highest-leverage next moves:** finish the generic determinant and
  first-cell identity bridge; use the weighted-L1 route to both H2b roots;
  isolate the shared real-horizon completion-index asymptotics to support
  both native rate roots. None of these steps supplies an independent
  opposing inequality or changes RH's OPEN status.
