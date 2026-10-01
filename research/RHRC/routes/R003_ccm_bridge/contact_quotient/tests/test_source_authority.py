from __future__ import annotations

import unittest

from source_authority_lint import lint


class SourceAuthorityTests(unittest.TestCase):
    def test_registered_proved_rows_resolve_to_lean_sources(self):
        lint()


if __name__ == "__main__":
    unittest.main()
