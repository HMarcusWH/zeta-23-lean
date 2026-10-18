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
    def test_latest_changes_requested_blocks_stale_approval(self):
        args = fixture()
        args[2].append(dict(args[2][0], id=124, state="CHANGES_REQUESTED",
                            submitted_at="2026-10-16T12:00:00Z", body="Please change."))
        with self.assertRaisesRegex(ValueError, "latest independent"):
            validate(*args, HEAD, TREE)

    def test_latest_commented_or_dismissed_blocks_stale_approval(self):
        for state in ("COMMENTED", "DISMISSED"):
            with self.subTest(state=state):
                args = fixture()
                args[2].append(dict(args[2][0], id=124, state=state,
                                    submitted_at="2026-10-16T12:00:00Z"))
                with self.assertRaisesRegex(ValueError, "latest independent"):
                    validate(*args, HEAD, TREE)

    def test_latest_unsigned_or_stale_approval_blocks(self):
        for changes in ({"body":"unsigned latest approval"},
                        {"commit_id":"c"*40}):
            with self.subTest(changes=changes):
                args=fixture()
                args[2].append(dict(args[2][0], id=124,
                                    submitted_at="2026-10-16T12:00:00Z", **changes))
                with self.assertRaisesRegex(ValueError, "latest independent"):
                    validate(*args, HEAD, TREE)

    def test_new_signed_approval_after_retraction_passes(self):
        args=fixture()
        args[2].append(dict(args[2][0], id=124, state="CHANGES_REQUESTED",
                            submitted_at="2026-10-16T12:00:00Z", body="Changes needed"))
        args[2].append(dict(args[2][0], id=125,
                            submitted_at="2026-10-17T12:00:00Z"))
        args[2].reverse()  # Ordering of GitHub pages is not an authority rule.
        self.assertEqual(validate(*args, HEAD, TREE)["github_review_id"], 125)

    def test_pending_draft_does_not_retract_submitted_approval(self):
        args=fixture()
        args[2].append(dict(args[2][0], id=124, state="PENDING",
                            submitted_at=None, body="Unsubmitted draft"))
        self.assertEqual(validate(*args, HEAD, TREE)["integrity_status"], "PASS")

    def test_invalid_or_ambiguous_review_metadata_fails_closed(self):
        for change in ({"id":123}, {"id":"124"},
                       {"submitted_at":"invalid"}, {"submitted_at":"2026-10-18T12:00:00"}):
            with self.subTest(change=change):
                args=fixture()
                candidate = dict(args[2][0])
                candidate.update(id=124, submitted_at="2026-10-18T12:00:00Z")
                candidate.update(change)
                args[2].append(candidate)
                with self.assertRaises(ValueError):
                    validate(*args, HEAD, TREE)

    def test_same_reviewer_dual_digest_latest_review(self):
        from verify_workflow_harvest import reviewer_receipt, digest
        from test_reviewed_workflow_harvest import fixture as harvest_fixture
        args=fixture()
        raw, harvest_review=harvest_fixture()
        harvest_review["reviewer_identity"]="independent_review_test"
        harvest_review["external_review_reference"]=args[0]["external_review_reference"]
        args[2][0]["body"] += "\nPR292-WORKFLOW-HARVEST-SHA256=" + digest(harvest_review)
        self.assertEqual(validate(*args, HEAD, TREE)["integrity_status"], "PASS")
        self.assertEqual(reviewer_receipt(harvest_review, args[1], args[2], args[3])["integrity_status"], "PASS")
        # The later review signs only the workflow digest: it must invalidate
        # the earlier field approval for this SAME reviewer.
        second_url = "https://github.com/HMarcusWH/zeta-23-lean/pull/292#pullrequestreview-124"
        args[2].append(dict(args[2][0], id=124, html_url=second_url,
            submitted_at="2026-10-17T12:00:00Z",
            body="PR292-WORKFLOW-HARVEST-SHA256=" + digest(harvest_review)))
        harvest_review["external_review_reference"] = second_url
        with self.assertRaisesRegex(ValueError, "latest independent"):
            validate(*args, HEAD, TREE)
        self.assertEqual(reviewer_receipt(harvest_review, args[1], args[2], args[3])["integrity_status"], "PASS")

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
