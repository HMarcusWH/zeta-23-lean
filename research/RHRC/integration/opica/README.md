# OPICA implementation

**Status: complete validation at the recorded earlier checkpoint.**
The [checkpoint report](POST_GREEN_RESEARCH.md) records PR head
`567d78de11ee3e3b7ae7e455fab0bf096ce90c34`, actual compiler checkout
`a6a4ce34cc82d5e54629ddfe6b013d8a92a18534`, their trees, complete compiler evidence
and the paginated workflow dispositions. It includes all 76 primary roots,
all 143 explicit consumers and every clause of the 25 paper families.
This status describes that checkpoint. A later publication head requires
fresh source/materialization receipts and workflow checks, retained
externally. Independent mathematical/human approval remains false; RH
and the existing closing obligations remain OPEN.

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
