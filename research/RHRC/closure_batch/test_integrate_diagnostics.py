from __future__ import annotations

import unittest

import integrate_diagnostics


class DiagnosticIntegrationTests(unittest.TestCase):
    def test_module_imports(self):
        self.assertTrue(callable(integrate_diagnostics.main))


if __name__ == "__main__":
    unittest.main()
