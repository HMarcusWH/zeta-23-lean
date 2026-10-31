import unittest
from research.RHRC.integration.opica_composition.contracts import StatementInventory,CohortInventory
from research.RHRC.integration.opica_composition.inventory import check_membership_coverage,contact_disposition

class InventoryCases(unittest.TestCase):
    def inventory(self,rows): return StatementInventory("a"*64,rows,"b"*64)
    def test_t05(self):
        expected=CohortInventory(["parent:r","followup:s","round3:t"])
        good=self.inventory([{"declaration":"r","membership_id":"parent:r"},
            {"declaration":"s","membership_id":"followup:s"},{"declaration":"t","membership_id":"round3:t"}])
        self.assertTrue(check_membership_coverage(good,expected).complete)
        bad=self.inventory(good.statements[:-1])
        self.assertEqual(check_membership_coverage(bad,expected).missing,["round3:t"])
    def test_t06(self):
        expected=CohortInventory(["parent:same","followup:same"])
        bad=self.inventory([{"declaration":"same","membership_id":"parent:same"}])
        self.assertFalse(check_membership_coverage(bad,expected).complete)
        both=self.inventory(bad.statements+[{"declaration":"same","membership_id":"followup:same"}])
        self.assertTrue(check_membership_coverage(both,expected).complete)
    def test_t07(self):
        old=self.inventory([{"declaration":"CCM"},{"declaration":"ExceptionalZero"}])
        self.assertFalse(check_membership_coverage(old,CohortInventory(["CCM","ExceptionalZero","OPICA","OPICAFollowup","OPICARound3"])).complete)
    def test_t08(self):
        contact={"producer":"old","consumer":"new"}
        self.assertEqual(contact_disposition(contact),"UNREVIEWED")
        self.assertNotIn("adapter",contact)
