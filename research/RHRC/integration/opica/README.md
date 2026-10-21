# OPICA implementation

**Status: kernel checks complete; integration and PR validation in progress.**
All 76 required primary declarations and all 143 explicit expected-type consumers
compile against the pinned Lean/Mathlib versions. The fresh historical native
build completed all 4,461 jobs, and the complete native adapter build completed
all 4,465 jobs. The required scope includes every clause of the 25 paper families
and the native source consumers. The complete six-target build/public export,
final registry audit, generated-state refresh and final PR workflow harvest
must finish before a green release is claimed.

The frozen `BUILD_SPEC.md`, `BUILD_MANIFEST.json`, `PUBLIC_ROOTS.json`,
`PAPER_CROSSWALK.json`, and paper inputs describe the supplied specification.
Their historical `SPECIFICATION_ONLY` / `PAPER` fields are preserved as source
evidence. They are not current compiler receipts. In particular, the earlier
document's statement that no repository work occurred applies to its own
preparation stage, not to the present implementation request.

The intended public import is `import Zeta23.OPICA`. Mathematical modules must
never import `Validation` or RHRC compiler instrumentation. The complete build and evidence commands are:

```sh
python research/RHRC/integration/opica/validate_contract.py --output-dir /tmp/opica
lake build Zeta23.OPICA Zeta23.OPICA.Validation Zeta23.RHRC.OpicaBindings \
  Zeta23.RHRC.RegisteredClaimBindings Zeta23.RHRC.DeclarationDependencyExport \
  Zeta23.RHRC.SourceCandidateResolution
python research/RHRC/integration/opica/check_exact.py
python -O research/RHRC/integration/opica/check_exact.py
python -m unittest discover -s research/RHRC/integration/opica/tests -v
python -O -m unittest discover -s research/RHRC/integration/opica/tests -v
python research/RHRC/integration/opica/build_receipt.py --output-dir /tmp/opica --requested-head HEAD --requested-base 97926d6a949fed7af0429a373b47abc772012834
python research/RHRC/integration/opica/validate_contract.py --phase release --formal-receipt /tmp/opica/compiler-receipt.json --output /tmp/opica/release-contract.json
```

Execution logs, type DAGs and final commit-bound receipts belong outside the
tracked repository. The exact finite checker reproduces 5,112 rational and
combinatorial assertions. Those assertions do not establish the analytic
theorems. A compiler receipt records exact types, constructors and TYPE / VALUE /
STRUCTURE dependencies; semantic review must still compare those types with
every paper clause. A theorem that assumes its intended conclusion is not
coverage.

The global theorem registry adds exactly 76 source-bound supporting laws after
full typed checks and exact root type/axiom review. It contains 198 claims and
194 proved bindings; all 122 historical claim objects, 118 historical binding
objects and four OPEN claims are preserved. RH, Step 4, A-X, B-Y,
C-Schur, OPEN-J46, native J5.2/MS1, contact-to-heat construction, D2 and independent
review gates retain their prior scope. Green component checks would not by
themselves approve a mathematical review or establish any of those native
premises.

The paper's Gaussian proof of the signed sinc/triangle pairing is implemented
with an alternate compact smooth approximate identity. The checked Fourier pair
is unchanged; the constructed Schwartz tests have a sinc-squared Fourier
majorant and a fixed compact spatial majorant, so dominated convergence applies
separately to both locally finite Jordan parts. This does not assume finite
global total variation. H2 retains the weighted estimate and also bounds the
whole off-lattice negative mass in ENNReal, including the infinite-mass case.

The proposed import graph in the frozen specification is a design input. The
actual source graph includes the affine transport import in the facade and the
weighted-L2 analytic continuation dependency in the Fejer layer. The static
contract checks the actual graph and its audit firewall. The actual project
imports are recorded separately in SOURCE_REGISTER, preserving the supplied
paper and specification bytes.

The documented receipt CLI also accepts `--manifest`, `--roots`, `--compiler-log`
and `--output`. It verifies a supplied log against a fresh build and export from
the same clean checkout. Logs require an explicit terminating completeness
record, every public mathematical declaration and constructor, all dependency
channels, and exact reviewed type digests for all primary roots.

The frozen blueprint assigned the two new native adapter files to
`RH_FORMAL_CORE`. The inherited source-candidate producer rejects every module
outside `Zeta23.CCM` and `Zeta23.ExceptionalZero` in that class, including already
registered theorems. The implementation therefore classifies only these two new
files as `AUXILIARY_FORMALIZATION` and records the exact two-path override in
SOURCE_REGISTER. Their `OPICA_SOURCE_BOUND_NATIVE_ADAPTER` semantic roles,
source-bound theorem registration, complete public dependency audit and typed
native consumers are retained. Every pre-existing file classification and the
protected producer remain unchanged.

New registry dependency lists are derived from all TYPE / VALUE / STRUCTURE
compiler uses, including transitive uses through unregistered helpers, mapped
against both the 118 historical bindings and the 76 OPICA bindings. Self and
unrelated identities are excluded. This records proof-use provenance; it does
not infer logical equivalence or prove any theorem antecedent. The release
contract compares those lists with the complete current compiler receipt.
