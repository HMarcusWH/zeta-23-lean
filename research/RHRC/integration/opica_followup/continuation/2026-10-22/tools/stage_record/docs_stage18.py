# Worked example from Stage 18 (copy into your scratch directory and adapt; see README.md here).
# Paths come from OPICA_REPO (repository root) and OPICA_SCRATCH (scratch directory).
from pathlib import Path
import os
REPO = Path(os.environ.get('OPICA_REPO', '/home/user/zeta-23-lean'))
C = REPO/'research/RHRC/integration/opica_followup/continuation/2026-10-22'
def edit(path, pairs):
    raw = path.read_bytes().decode()
    crlf = '\r\n' in raw
    for old, new in pairs:
        if crlf:
            old, new = old.replace('\n', '\r\n'), new.replace('\n', '\r\n')
        assert raw.count(old) == 1, (path, old[:70])
        raw = raw.replace(old, new)
    path.write_bytes(raw.encode())

edit(REPO/'AGENTS.md', [(
"Forty-eight additional roots passed narrow gates and 11 original roots still lack\n"
"complete implementations. Read the continuation STAGE17_HANDOVER.md (and the",
"Forty-nine additional roots passed narrow gates and 10 original roots still lack\n"
"complete implementations. Read the continuation STAGE18_HANDOVER.md (and the")])

edit(C/'README.md', [
("The latest [Stage 17 handover](STAGE17_HANDOVER.md) records the generic forced resolvent: the unique\n",
 "The latest [Stage 18 handover](STAGE18_HANDOVER.md) records the multiplicity-sensitive zero-jet\n"
 "measures: the normalized κ-jets below the actual multiplicity are gapped self-dual measures (R2-H1).\n"
 "[Stage 17](STAGE17_HANDOVER.md) records the generic forced resolvent: the unique\n"),
("axioms and aggregate acceptance. `REMAINING_WORK.md` lists the 11 absent proofs.",
 "axioms and aggregate acceptance. `REMAINING_WORK.md` lists the 10 absent proofs."),
("- Forty-eight additional original roots passed independent local module, full-type/",
 "- Forty-nine additional original roots passed independent local module, full-type/"),
("  square-defect roots (Stage 16) and the two boundary-amplitude roots (Stage 17);\n"
 "  aggregate and full acceptance remain pending.\n"
 "- 11 original primary implementations are still absent.",
 "  square-defect roots (Stage 16), the two boundary-amplitude roots (Stage 17) and\n"
 "  the zero-jet root (Stage 18); aggregate and full acceptance remain pending.\n"
 "- 10 original primary implementations are still absent."),
("Complete the 11 absent roots without replacing them by supporting lemmas.",
 "Complete the 10 absent roots without replacing them by supporting lemmas."),
("roots (Stage 16) and the two boundary-amplitude roots (Stage 17) now have narrow gates.",
 "roots (Stage 16), the two boundary-amplitude roots (Stage 17) and the zero-jet root\n"
 "(Stage 18) now have narrow gates."),
])

edit(C/'REMAINING_WORK.md', [
("- 48: `PROVED_NARROW_LOCAL_GATES_AGGREGATE_PENDING`,",
 "- 49: `PROVED_NARROW_LOCAL_GATES_AGGREGATE_PENDING`,"),
("and the [Stage 17](STAGE17_HANDOVER.md) generic forced profile and boundary amplitude\n- 11: `OPEN_NO_COMPLETE_CANDIDATE`",
 "the [Stage 17](STAGE17_HANDOVER.md) generic forced profile and boundary amplitude, and the [Stage 18](STAGE18_HANDOVER.md) multiplicity-sensitive zero-jet measures\n- 10: `OPEN_NO_COMPLETE_CANDIDATE`"),
("## 11 roots without complete candidate implementations",
 "## 10 roots without complete candidate implementations"),
("### Zeta23.OPICAFollowup.CoPoissonJets\n\n- `copoisson_zero_jets_measures`\n\n", ""),
("Implement the 11 absent roots above. Forty-eight roots now have narrow module,",
 "Implement the 10 absent roots above. Forty-nine roots now have narrow module,"),
("and two Stage 17 roots (generic forced profile, boundary amplitude) are documented separately.",
 "two Stage 17 roots (generic forced profile, boundary amplitude) and one Stage 18 root (zero-jet measures) are documented separately."),
("all four SquareDefect roots and both BoundaryAmplitude roots now have narrow gates;",
 "all four SquareDefect roots, both BoundaryAmplitude roots and the CoPoissonJets root now have narrow gates;"),
("square-defect and boundary-amplitude formalization choices",
 "square-defect, boundary-amplitude and zero-jet formalization choices"),
])

edit(C/'DOCUMENTATION_INDEX.md', [
("checkpoint and its staged repairs; read [STAGE17_HANDOVER.md](STAGE17_HANDOVER.md)",
 "checkpoint and its staged repairs; read [STAGE18_HANDOVER.md](STAGE18_HANDOVER.md)"),
("[Stage 17](STAGE17_HANDOVER.md) proves both BoundaryAmplitude roots (F3): for any 1/2 < Re rho < 1,",
 "[Stage 18](STAGE18_HANDOVER.md) proves the CoPoissonJets root (R2-H1): at an actual strip zero of\n"
 "multiplicity m, every normalized kappa-jet below m of the actual construction is a gapped, even,\n"
 "Fourier self-dual measure with linear growth and the differentiated forced chain; the\n"
 "[evidence](evidence/current-codex/stage18/STATUS.json) binds every log and source.\n"
 "[Stage 17](STAGE17_HANDOVER.md) proves both BoundaryAmplitude roots (F3): for any 1/2 < Re rho < 1,"),
])
print('docs edited')
