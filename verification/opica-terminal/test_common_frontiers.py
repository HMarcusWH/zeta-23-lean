"""Mock orchestration controls. No fixture is a mathematical proof receipt."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
SCRIPT = HERE/"run_common.sh"

class FrontierControls(unittest.TestCase):
    def execute(self, fail="", bad_audit="", missing_receipt=False, fail_controls=False, native_mode=False):
        with tempfile.TemporaryDirectory() as td:
            p = Path(td)
            work, native, out, bin_dir = (p/x for x in ("original","native","result","bin"))
            for d in (work,native,bin_dir):
                d.mkdir()
            scripts_dir=native/"verification/opica-terminal"
            scripts_dir.mkdir(parents=True)
            shutil.copy(HERE/"frontier_helpers.sh",scripts_dir)
            (scripts_dir/"run_auditor_tests.sh").write_text(
                "#!/bin/sh\n[ \"$FAIL_CONTROLS\" = 1 ] && exit 8\nprintf '%s\\n' OPICA_TERMINAL_AUDITOR_CONTROLS_PASS\n")
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
                "python3": """#!/bin/sh
case "$1" in -) cat >/dev/null;; *) printf '%s\\n' verify >> "$TRACE"
  if [ "$MISSING_RECEIPT" != 1 ]; then
    while [ "$#" -gt 0 ]; do
      if [ "$1" = --output ]; then shift; printf '{}\\n' > "$1"; break; fi
      shift
    done
  fi;;
esac
exit 0
""",
            }
            for name, content in scripts.items():
                path = bin_dir/name
                path.write_text(content)
                path.chmod(0o755)
            env = {**os.environ, "PATH":str(bin_dir)+os.pathsep+os.environ["PATH"],
                   "TRACE":str(trace),"FAIL_BUILD":fail,"BAD_AUDIT":bad_audit,
                   "MISSING_RECEIPT":str(int(missing_receipt)),"FAIL_CONTROLS":str(int(fail_controls))}
            cmd= ["bash",str(HERE/"run_native.sh"),str(out)] if native_mode else ["bash",str(SCRIPT),str(native),str(source),str(out)]
            proc = subprocess.run(cmd,cwd=native if native_mode else work,env=env,capture_output=True,text=True)
            statuses = {f.stem:f.read_text().strip() for f in out.glob("*.status")}
            calls = trace.read_text().splitlines() if trace.exists() else []
            return proc, statuses, calls, (out/"evidence.json").is_file()

    def test_native_failure_still_checks_both_arithmetic_frontiers(self):
        p,s,c,e = self.execute(fail="Zeta23.OPICATerminal.LiteralEnergyGrowth")
        self.assertNotEqual(p.returncode,0)
        self.assertEqual(s["native-math"],"native-math exit=7")
        self.assertEqual(s["host-math"],"host-math exit=0")
        self.assertEqual(s["topg-math"],"topg-math exit=0")
        self.assertEqual(s["closed-principal-math"],"closed-principal-math exit=0")
        self.assertIn("skipped",s["terminal-math"])
        self.assertNotIn("verify",c)
        self.assertFalse(e)

    def test_host_math_failure_still_checks_topg(self):
        p,s,c,e = self.execute(fail="OPICATerminalSupplier.PrincipalHost")
        self.assertNotEqual(p.returncode,0)
        self.assertEqual(s["host-math"],"host-math exit=7")
        self.assertEqual(s["topg-audit"],"topg-audit exit=0")
        self.assertIn("skipped",s["closed-principal-math"])
        self.assertNotIn("build OPICATerminalSupplier.ClosedPrincipal",c)
        self.assertNotIn("verify",c)

    def test_host_audit_failure_does_not_hide_math(self):
        p,s,c,e = self.execute(fail="OPICATerminalSupplier.AuditHost")
        self.assertNotEqual(p.returncode,0)
        self.assertEqual(s["host-math"],"host-math exit=0")
        self.assertEqual(s["host-audit"],"host-audit exit=7")
        self.assertEqual(s["closed-principal-math"],"closed-principal-math exit=0")
        self.assertEqual(s["terminal-math"],"terminal-math exit=0")
        self.assertEqual(s["terminal-audit"],"terminal-audit exit=0")
        self.assertNotIn("verify",c)
        self.assertFalse(e)

    def test_bad_audit_is_not_masked(self):
        p,s,c,e = self.execute(bad_audit="src/OPICATerminalSupplier/AuditTopG.lean")
        self.assertNotEqual(p.returncode,0)
        self.assertEqual(s["topg-audit"],"topg-audit exit=1")
        self.assertEqual(s["terminal-math"],"terminal-math exit=0")
        self.assertNotIn("verify",c)

    def test_failed_controls_still_collect_math_but_block_receipt(self):
        p,s,c,e = self.execute(fail_controls=True)
        self.assertNotEqual(p.returncode,0)
        self.assertEqual(s["auditor-controls"],"auditor-controls exit=8")
        self.assertEqual(s["terminal-math"],"terminal-math exit=0")
        self.assertNotIn("verify",c)

    def test_missing_receipt_fails_closed(self):
        p,s,c,e = self.execute(missing_receipt=True)
        self.assertNotEqual(p.returncode,0)
        self.assertEqual(s["receipt"],"receipt exit=1")
        self.assertFalse(e)

    def test_all_success_reaches_terminal_and_receipt(self):
        p,s,c,e = self.execute()
        self.assertEqual(p.returncode,0,p.stderr)
        self.assertIn("build OPICATerminalSupplier.Terminal",c)
        self.assertIn("build OPICATerminalSupplier.AuditTerminal",c)
        self.assertEqual(c[-1],"verify")
        self.assertTrue(e)

    def test_native_audit_failure_separate_from_math(self):
        p,s,c,e = self.execute(native_mode=True,fail="Zeta23.OPICATerminal.AuditNative")
        self.assertNotEqual(p.returncode,0)
        self.assertEqual(s["native-math"],"native-math exit=0")
        self.assertEqual(s["native-audit"],"native-audit exit=7")
        self.assertNotIn("verify",c)

    def test_native_success(self):
        p,s,c,e = self.execute(native_mode=True)
        self.assertEqual(p.returncode,0,p.stderr)
        self.assertTrue(e)

if __name__=="__main__":
    unittest.main()
