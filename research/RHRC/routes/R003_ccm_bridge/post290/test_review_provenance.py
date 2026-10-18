#!/usr/bin/env python3
"""Synthetic independent-review approval tests; not mathematical authority."""
import copy
import unittest
from verify_semantic_review_provenance import (
    validate,field_digest,semantic_review_digest,SEMANTIC_REVIEW_TOKEN_PREFIX)

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
    pr={"number":292,"head":{"sha":HEAD},"user":{"login":"source_author"},"commits":1}
    github=[{"id":123,"html_url":url,"state":"APPROVED",
             "commit_id":HEAD,"submitted_at":"2026-10-15T12:00:00Z",
             "user":{"login":"independent_review_test","type":"User"},
             "author_association":"COLLABORATOR",
             "body":SEMANTIC_REVIEW_TOKEN_PREFIX+semantic_review_digest(review)}]
    commits=[{"author":{"login":"source_author"},"committer":{"login":"ci_author"}}]
    return [review,pr,github,commits]

class ReviewerProvenanceTests(unittest.TestCase):
    def test_exact_review_succeeds_only_as_synthetic_control(self):
        self.assertEqual(validate(*fixture(),HEAD,TREE)["integrity_status"],"PASS")
    def test_full_review_and_component_hashes_are_both_receipted(self):
        args=fixture();receipt=validate(*args,HEAD,TREE)
        self.assertEqual(receipt["field_reviews_sha256"],field_digest(args[0]["field_reviews"]))
        self.assertEqual(receipt["semantic_review_sha256"],semantic_review_digest(args[0]))
        self.assertTrue(receipt["source_commit_authorship_verified"])
        self.assertEqual(receipt["source_commit_count"],1)
    def test_legacy_field_only_signature_is_not_full_review_approval(self):
        args=fixture()
        args[2][0]["body"]="PR292-44-FIELD-SHA256="+field_digest(args[0]["field_reviews"])
        with self.assertRaisesRegex(ValueError,"latest independent"):
            validate(*args,HEAD,TREE)
    def test_false_assumption_decision_cannot_be_flipped_after_signature(self):
        args=fixture();args[0]["independent_assumption_review_pass"]=False
        args[2][0]["body"]=SEMANTIC_REVIEW_TOKEN_PREFIX+semantic_review_digest(args[0])
        with self.assertRaises(ValueError):validate(*args,HEAD,TREE)
        args[0]["independent_assumption_review_pass"]=True
        with self.assertRaisesRegex(ValueError,"latest independent"):
            validate(*args,HEAD,TREE)
        args[2][0]["body"]=SEMANTIC_REVIEW_TOKEN_PREFIX+semantic_review_digest(args[0])
        self.assertEqual(validate(*args,HEAD,TREE)["integrity_status"],"PASS")
    def test_all_payload_fields_except_review_url_are_signed(self):
        args=fixture();original=semantic_review_digest(args[0])
        for key,value in (("schema_version","changed"),("reviewed_head","c"*40),
                ("reviewed_tree","c"*40),("claim_cap","changed"),
                ("reviewer_identity","other"),("reviewer_is_source_author",True),
                ("independent_assumption_review_pass",False),("future_security_decision",False)):
            with self.subTest(key=key):
                review=copy.deepcopy(args[0]);review[key]=value
                self.assertNotEqual(semantic_review_digest(review),original)
        changed=copy.deepcopy(args[0]);changed["external_review_reference"]="eventual URL"
        self.assertEqual(semantic_review_digest(changed),original)
        reordered=dict(reversed(list(args[0].items())))
        self.assertEqual(semantic_review_digest(reordered),original)
    def test_unattributed_author_or_committer_fails_closed(self):
        for role in ("author","committer"):
            for account in (None,{}, {"login":None},{"login":""},{"login":" "},
                            {"login":True},[],"unlinked"):
                with self.subTest(role=role,account=account):
                    args=fixture();args[3][0][role]=account
                    with self.assertRaisesRegex(ValueError,"unattributed GitHub"):
                        validate(*args,HEAD,TREE)
            args=fixture();del args[3][0][role]
            with self.assertRaisesRegex(ValueError,"unattributed GitHub"):
                validate(*args,HEAD,TREE)
        args=fixture();args[3]=[]
        with self.assertRaisesRegex(ValueError,"authorship inventory"):
            validate(*args,HEAD,TREE)
    def test_attributed_bot_source_participant_remains_recorded(self):
        args=fixture();args[3][0]["committer"]={"login":"github-actions[bot]","type":"Bot"}
        self.assertEqual(validate(*args,HEAD,TREE)["integrity_status"],"PASS")
    def test_source_commit_inventory_count_must_be_complete(self):
        for count in (None,True,0,-1,"1",2,250,251):
            with self.subTest(count=count):
                args=fixture();args[1]["commits"]=count
                with self.assertRaisesRegex(ValueError,"inventory incomplete or count mismatched"):
                    validate(*args,HEAD,TREE)
        args=fixture();del args[1]["commits"]
        with self.assertRaisesRegex(ValueError,"inventory incomplete or count mismatched"):
            validate(*args,HEAD,TREE)
        args=fixture();args[3].append(copy.deepcopy(args[3][0]));args[1]["commits"]=2
        self.assertEqual(validate(*args,HEAD,TREE)["source_commit_count"],2)
    def test_authorized_independent_repository_associations(self):
        for association in ("OWNER", "MEMBER", "COLLABORATOR"):
            with self.subTest(association=association):
                args = fixture()
                args[2][0]["author_association"] = association
                receipt = validate(*args, HEAD, TREE)
                self.assertEqual(receipt["integrity_status"], "PASS")
                self.assertEqual(receipt["reviewer_author_association"], association)
                self.assertEqual(receipt["reviewer_account_type"], "User")

    def test_unauthorized_or_malformed_repository_association_rejected(self):
        for association in ("NONE", "CONTRIBUTOR", "FIRST_TIMER", "FIRST_TIME_CONTRIBUTOR",
                            "BOT", "UNKNOWN", "collaborator", "COLLABORATOR ",
                            None, True, 1, [], {}):
            with self.subTest(association=association):
                args = fixture()
                args[2][0]["author_association"] = association
                with self.assertRaisesRegex(ValueError, "not repository-authorized"):
                    validate(*args, HEAD, TREE)
        args = fixture()
        del args[2][0]["author_association"]
        with self.assertRaisesRegex(ValueError, "not repository-authorized"):
            validate(*args, HEAD, TREE)

    def test_authorized_association_does_not_make_nonhuman_account_eligible(self):
        for account_type in ("Bot", "Mannequin", "Organization", "user", None, True, []):
            with self.subTest(account_type=account_type):
                args = fixture()
                args[2][0]["user"]["type"] = account_type
                with self.assertRaisesRegex(ValueError, "not an authenticated GitHub User"):
                    validate(*args, HEAD, TREE)
        args = fixture()
        del args[2][0]["user"]["type"]
        with self.assertRaisesRegex(ValueError, "not an authenticated GitHub User"):
            validate(*args, HEAD, TREE)

    def test_unauthorized_latest_review_cannot_fall_back_to_older_authorized(self):
        for changes in ({"author_association": "NONE"},
                        {"user": {"login": "independent_review_test", "type": "Bot"}}):
            with self.subTest(changes=changes):
                args = fixture()
                latest = dict(args[2][0], id=124, submitted_at="2026-10-17T12:00:00Z", **changes)
                args[2].append(latest)
                with self.assertRaisesRegex(ValueError, "not repository-authorized|not an authenticated GitHub"):
                    validate(*args, HEAD, TREE)
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
        a[2][0]["author_association"]="OWNER"
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
