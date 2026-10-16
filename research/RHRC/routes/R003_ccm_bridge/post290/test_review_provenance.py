#!/usr/bin/env python3
"""Synthetic independent-review approval tests; not mathematical authority."""
import copy
import unittest
from verify_semantic_review_provenance import validate,field_digest

HEAD="a"*40
TREE="b"*40
FIELDS=[{"id":f"N{i:02d}","declaration_ref":"Mock.lean", "semantic_proof_review":"PASS",
         "evidence_verified":True,"reason":"Synthetic test evidence only"} for i in range(1,41)] + [
        {"id":f"G{i:02d}","declaration_ref":"Mock.lean","semantic_proof_review":"PASS",
         "evidence_verified":True,"reason":"Synthetic test evidence only"} for i in range(1,5)]

def fixture():
    url="https://github.com/HMarcusWH/zeta-23-lean/pull/292#pullrequestreview-123"
    review={"schema_version":"POST290_INDEPENDENT_SEMANTIC_REVIEW_1.0",
        "reviewed_head":HEAD,"reviewed_tree":TREE,"claim_cap":"RH_OPEN",
        "reviewer_is_source_author":False,"independent_assumption_review_pass":True,
        "reviewer_identity":"independent_review_test",
        "external_review_reference":url,"field_reviews":copy.deepcopy(FIELDS)}
    pr={"number":292,"head":{"sha":HEAD},"user":{"login":"source_author"}}
    github=[{"id":123,"html_url":url,"state":"APPROVED",
             "commit_id":HEAD,"submitted_at":"2026-10-15T12:00:00Z",
             "user":{"login":"independent_review_test"},
             "body":"PR292-44-FIELD-SHA256="+field_digest(review["field_reviews"])}]
    commits=[{"author":{"login":"source_author"},"committer":{"login":"ci_author"}}]
    return [review,pr,github,commits]

class ReviewerProvenanceTests(unittest.TestCase):
    def test_exact_review_succeeds_only_as_synthetic_control(self):
        self.assertEqual(validate(*fixture(),HEAD,TREE)["integrity_status"],"PASS")
    def test_source_author_cannot_review(self):
        a=fixture();a[0]["reviewer_identity"]="source_author";a[2][0]["user"]["login"]="source_author"
        with self.assertRaises(ValueError):validate(*a,HEAD,TREE)
    def test_stale_commit_rejected(self):
        a=fixture();a[2][0]["commit_id"]="c"*40
        with self.assertRaises(ValueError):validate(*a,HEAD,TREE)
    def test_field_mutation_invalidates_approval_digest(self):
        a=fixture();a[0]["field_reviews"][3]["reason"]="Changed after approval"
        with self.assertRaises(ValueError):validate(*a,HEAD,TREE)
    def test_missing_field_rejected(self):
        a=fixture();a[0]["field_reviews"].pop()
        with self.assertRaises(ValueError):validate(*a,HEAD,TREE)
    def test_unsigned_approval_rejected(self):
        a=fixture();a[2][0]["body"]="APPROVED without field review"
        with self.assertRaises(ValueError):validate(*a,HEAD,TREE)
    def test_unverified_reviewer_identity_rejected(self):
        a=fixture();a[0]["reviewer_is_source_author"]=None
        with self.assertRaises(ValueError):validate(*a,HEAD,TREE)

if __name__=="__main__":
    unittest.main()
