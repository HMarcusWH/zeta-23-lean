"""Mock orchestration controls. No fixture is a mathematical proof receipt."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().with_name("run_common.sh")

class FrontierControls(unittest.TestCase):
    def execute(self, fail="", bad_audit=""):
        with tempfile.TemporaryDirectory() as td:
            p = Path(td)
            work, native, out, bin_dir = (p/x for x in ("original","native","result","bin"))
            for d in (work,native,bin_dir):
                d.mkdir()
            (work/"lean-toolchain").write_text("leanprover/lean4:v4.33.1\n")
            (work/"lake-manifest.json").write_text('{"packages":[]}\n')
            source = p/"source.json"
            source.write_text("{}\n")
            trace = p/"trace"
            scripts = {
                "git": '#!/bin/sh\nprintf "%s\\n" 0df444a360eaa60ab8c11dca51a86af692955474\n',
                "lake": """#!/bin/sh
printf '%s\\n' "$*" >> "$TRACE"
if [ "$1" = build ] && [ "$2" = "$FAIL_BUILD" ]; then exit 7; fi
if [ "$1" = env ] && [ "$3" = "$BAD_AUDIT" ]; then echo 'error: mock audit'; fi
exit 0
""",
                # The external Python verification is mocked independently
                # from the real shell orchestration under test.
                "python3": """#!/bin/sh
case "$1" in -) cat >/dev/null;; *) printf '%s\\n' verify >> "$TRACE";; esac
exit 0
""",
            }
            for name, content in scripts.items():
                path = bin_dir/name
                path.write_text(content)
                path.chmod(0o755)
            env = {**os.environ, "PATH":str(bin_dir)+os.pathsep+os.environ["PATH"],
                   "TRACE":str(trace),"FAIL_BUILD":fail,"BAD_AUDIT":bad_audit}
            proc = subprocess.run(["bash",str(SCRIPT),str(native),str(source),str(out)],
                                  cwd=work,env=env,capture_output=True,text=True)
            statuses = {f.stem:f.read_text().strip() for f in out.glob("*.status")}
            calls = trace.read_text().splitlines() if trace.exists() else []
            return proc, statuses, calls

    def test_native_failure_still_checks_both_arithmetic_frontiers(self):
        p,s,c = self.execute(fail="Zeta23.OPICATerminal.LiteralEnergyGrowth")
        self.assertNotEqual(p.returncode,0)
        self.assertEqual(s["native"],"native exit=7")
        self.assertEqual(s["host"],"host exit=0")
        self.assertEqual(s["topg"],"topg exit=0")
        self.assertEqual(s["closed-principal"],"closed-principal exit=0")
        self.assertNotIn("build OPICATerminalSupplier.AuditTerminal",c)
        self.assertNotIn("verify",c)

    def test_host_failure_still_checks_topg(self):
        p,s,c = self.execute(fail="OPICATerminalSupplier.AuditHost")
        self.assertNotEqual(p.returncode,0)
        self.assertEqual(s["host"],"host exit=7")
        self.assertEqual(s["topg"],"topg exit=0")
        self.assertIn("skipped",s["closed-principal"])
        self.assertNotIn("build OPICATerminalSupplier.ClosedPrincipal",c)
        self.assertNotIn("verify",c)

    def test_bad_audit_is_not_masked(self):
        p,s,c = self.execute(bad_audit="src/OPICATerminalSupplier/AuditTopG.lean")
        self.assertNotEqual(p.returncode,0)
        self.assertEqual(s["topg"],"topg exit=1")
        self.assertNotIn("verify",c)

    def test_all_success_reaches_terminal_and_receipt(self):
        p,s,c = self.execute()
        self.assertEqual(p.returncode,0,p.stderr)
        self.assertIn("build OPICATerminalSupplier.AuditTerminal",c)
        self.assertEqual(c[-1],"verify")

if __name__=="__main__":
    unittest.main()
