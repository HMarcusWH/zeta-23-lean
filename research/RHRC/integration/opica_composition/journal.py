"""External SQLite journal with durable dispatch and verifier-owned publication.

Hash chains detect corruption; they do not prove mathematics. Only the trusted
publisher replays Lean and obtains the private publication capability. All
candidate-facing operations accept data, never a checker or a PASS flag.
"""
from __future__ import annotations
from contextlib import contextmanager
import hashlib
import os
from pathlib import Path
import sqlite3
import uuid
from .canonical import (canonical_bytes, load_bytes, digest, digest_text,
                        require, nonempty_text, relative_path)

ZERO = "0" * 64
KINDS = frozenset({"GENERATION_STARTED", "PROPOSAL", "ATTEMPT_STARTED", "ADAPTER_REQUIRED",
    "APPLICATION_VERIFIED", "APPLICATION_REJECTED", "RESOURCE_EXHAUSTED",
    "COUNTERMODEL_VERIFIED", "GENERATION_INVALIDATED", "EVIDENCE_ARCHIVED", "REVIEW_RECORDED"})
_PUBLISH = object()

def _no_links(path: Path) -> None:
    for parent in (path, *path.parents):
        require(not parent.is_symlink(), "linked journal/artifact path forbidden")

class Journal:
    def __init__(self, path: Path, *, repository: Path | None = None):
        self.path = Path(path).absolute()
        _no_links(self.path)
        repository = (repository or Path(__file__).resolve().parents[4]).resolve()
        require(not self.path.resolve().is_relative_to(repository), "runtime journal must be outside source")
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.db = sqlite3.connect(self.path, timeout=10, isolation_level=None)
        self.db.row_factory = sqlite3.Row
        self.db.execute("PRAGMA journal_mode=WAL")
        self.db.execute("PRAGMA synchronous=FULL")
        self.db.execute("PRAGMA foreign_keys=ON")
        self.db.executescript('''
          CREATE TABLE IF NOT EXISTS state(singleton INTEGER PRIMARY KEY CHECK(singleton=1),
            revision INTEGER NOT NULL,generation TEXT,source TEXT,profile TEXT,last_hash TEXT NOT NULL);
          INSERT OR IGNORE INTO state VALUES(1,0,NULL,NULL,NULL,printf('%064d',0));
          CREATE TABLE IF NOT EXISTS generations(generation TEXT PRIMARY KEY,source TEXT NOT NULL,profile TEXT NOT NULL);
          CREATE TABLE IF NOT EXISTS events(revision INTEGER PRIMARY KEY,event_id TEXT UNIQUE NOT NULL,
            body BLOB NOT NULL,event_hash TEXT UNIQUE NOT NULL);
          CREATE TABLE IF NOT EXISTS menus(generation TEXT PRIMARY KEY,body BLOB NOT NULL,digest TEXT NOT NULL);
          CREATE TABLE IF NOT EXISTS attempts(attempt_id TEXT PRIMARY KEY,generation TEXT NOT NULL,
            source TEXT NOT NULL,action_id TEXT NOT NULL,proposal TEXT NOT NULL,
            start_revision INTEGER NOT NULL,status TEXT NOT NULL,evidence TEXT);
          CREATE TABLE IF NOT EXISTS applications(application_id TEXT PRIMARY KEY,attempt_id TEXT UNIQUE NOT NULL,
            generation TEXT NOT NULL,source TEXT NOT NULL,body BLOB NOT NULL);
        ''')
        self.verify_chain()

    def close(self): self.db.close()
    def __enter__(self): return self
    def __exit__(self, *_): self.close()

    def state(self) -> dict:
        return dict(self.db.execute("SELECT * FROM state WHERE singleton=1").fetchone())

    @contextmanager
    def _transaction(self, *, expected_revision: int, generation=None, source=None):
        require(type(expected_revision) is int and expected_revision >= 0, "integer CAS revision required")
        self.db.execute("BEGIN IMMEDIATE")
        try:
            state = self.verify_chain()
            require(state["revision"] == expected_revision, "stale journal revision")
            if generation is not None:
                require(state["generation"] == generation and state["source"] == source,
                        "stale source generation")
            yield state
            self.db.execute("COMMIT")
        except BaseException:
            self.db.execute("ROLLBACK")
            raise

    def _event(self, state: dict, kind: str, payload: dict, *, event_id=None,
               generation=None, source=None) -> dict:
        require(kind in KINDS, "unknown journal event")
        body = {"schema": "OPICA_JOURNAL_EVENT_V2", "revision": state["revision"] + 1,
                "previous": state["last_hash"], "event_id": event_id or uuid.uuid4().hex,
                "kind": kind, "generation": generation or state["generation"],
                "source": source or state["source"], "payload": payload}
        nonempty_text(body["event_id"], "event ID")
        event_hash = digest(body, domain="OPICA_JOURNAL_EVENT_V2")
        self.db.execute("INSERT INTO events VALUES(?,?,?,?)",
                        (body["revision"], body["event_id"], canonical_bytes(body), event_hash))
        self.db.execute("UPDATE state SET revision=?,last_hash=? WHERE singleton=1",
                        (body["revision"], event_hash))
        return {**body, "event_hash": event_hash}

    def activate(self, generation: str, source: str, profile: str, *, expected_revision: int):
        for value in (generation, source, profile): digest_text(value)
        with self._transaction(expected_revision=expected_revision) as state:
            require(state["generation"] is None, "invalidate the active generation before activation")
            require(self.db.execute("SELECT 1 FROM generations WHERE generation=?", (generation,)).fetchone() is None,
                    "generation reactivation forbidden")
            self.db.execute("INSERT INTO generations VALUES(?,?,?)", (generation, source, profile))
            event = self._event(state, "GENERATION_STARTED", {"profile": profile}, generation=generation, source=source)
            self.db.execute("UPDATE state SET generation=?,source=?,profile=? WHERE singleton=1",
                            (generation, source, profile))
        return event

    def freeze_menu(self, actions: list, expected_ids: frozenset[str], *, generation: str,
                    source: str, expected_revision: int):
        from research.RHRC.permansson.opica_composition import select_action
        select_action(actions, source=source, allowed_ids=expected_ids,
                      attempt_counts={name: 0 for name in expected_ids}, budget=0)
        rows = [{"action_id": a.action_id, "source": a.source,
                 "priority": a.priority, "cost": a.cost} for a in sorted(actions, key=lambda a: a.action_id)]
        body = {"actions": rows, "eligible_ids": sorted(expected_ids)}
        menu_hash = digest(body, domain="OPICA_MENU_V1")
        with self._transaction(expected_revision=expected_revision, generation=generation, source=source) as state:
            require(self.db.execute("SELECT 1 FROM menus WHERE generation=?", (generation,)).fetchone() is None,
                    "menu changed inside a generation")
            self.db.execute("INSERT INTO menus VALUES(?,?,?)", (generation, canonical_bytes(body), menu_hash))
            self._event(state, "REVIEW_RECORDED", {"kind": "MENU_FROZEN", "menu": menu_hash})
        return menu_hash

    def attempt_counts(self, generation: str) -> dict[str, int]:
        row = self.db.execute("SELECT body FROM menus WHERE generation=?", (generation,)).fetchone()
        require(row is not None, "eligible menu not frozen")
        counts = {name: 0 for name in load_bytes(row[0])["eligible_ids"]}
        for r in self.db.execute("SELECT action_id,count(*) AS n FROM attempts WHERE generation=? GROUP BY action_id",
                                 (generation,)):
            require(r["action_id"] in counts, "attempt outside frozen menu")
            counts[r["action_id"]] = r["n"]
        return counts

    def dispatch(self, proposals: dict[str, str], budget: int, *, generation: str,
                 source: str, expected_revision: int) -> dict:
        """Selection and attempt-start commit atomically before a worker is released."""
        from research.RHRC.permansson.opica_composition import Action, select_action
        require(type(proposals) is dict, "complete proposal map required")
        with self._transaction(expected_revision=expected_revision, generation=generation, source=source) as state:
            menu = self.db.execute("SELECT body,digest FROM menus WHERE generation=?", (generation,)).fetchone()
            require(menu is not None, "eligible menu not frozen")
            body = load_bytes(menu["body"])
            require(digest(body, domain="OPICA_MENU_V1") == menu["digest"], "menu corruption")
            require(set(proposals) == set(body["eligible_ids"]), "proposal/menu mismatch")
            for value in proposals.values(): digest_text(value, "proposal")
            choice = select_action([Action(**r) for r in body["actions"]], source=source,
                allowed_ids=frozenset(body["eligible_ids"]), attempt_counts=self.attempt_counts(generation), budget=budget)
            if choice["kind"] == "STOP":
                return {**choice, "revision": state["revision"], "menu": menu["digest"]}
            attempt_id = uuid.uuid4().hex
            event = self._event(state, "ATTEMPT_STARTED", {"attempt_id": attempt_id,
                "action_id": choice["action_id"], "proposal": proposals[choice["action_id"]],
                "menu": menu["digest"], "budget": budget})
            self.db.execute("INSERT INTO attempts VALUES(?,?,?,?,?,?,?,NULL)",
                (attempt_id, generation, source, choice["action_id"], proposals[choice["action_id"]],
                 event["revision"], "STARTED"))
        return {**choice, "attempt_id": attempt_id, "revision": event["revision"],
                "menu": menu["digest"], "proposal": proposals[choice["action_id"]]}

    def record_outcome(self, attempt_id: str, status: str, payload: dict, *, generation: str,
                       source: str, expected_revision: int):
        mapping = {"ADAPTER_REQUIRED": "ADAPTER_REQUIRED", "UNRESOLVED": "APPLICATION_REJECTED",
                   "TYPE_REJECTED_THIS_APPLICATION": "APPLICATION_REJECTED",
                   "RESOURCE_EXHAUSTED": "RESOURCE_EXHAUSTED", "ENVIRONMENT_ERROR": "APPLICATION_REJECTED"}
        require(status in mapping, "positive proof outcomes require trusted verifier publication")
        with self._transaction(expected_revision=expected_revision, generation=generation, source=source) as state:
            row = self.db.execute("SELECT * FROM attempts WHERE attempt_id=?", (attempt_id,)).fetchone()
            require(row is not None and row["generation"] == generation and row["source"] == source,
                    "unknown/stale attempt")
            require(row["status"] == "STARTED", "attempt already completed")
            event = self._event(state, mapping[status], {"attempt_id": attempt_id, "status": status, "details": payload})
            self.db.execute("UPDATE attempts SET status=? WHERE attempt_id=?", (status, attempt_id))
        return event

    def _publish(self, token, attempt_id: str, application: dict, *, generation: str,
                 source: str, expected_revision: int):
        require(token is _PUBLISH, "publication capability required")
        require(application.get("status") == "PROVED_CONDITIONAL" and
                application.get("publication_eligible") is True,
                "application has not passed production native replay")
        require(application.get("source_generation") == generation, "application source generation differs")
        app_id = digest(application, domain="OPICA_PUBLISHED_APPLICATION_V1")
        with self._transaction(expected_revision=expected_revision, generation=generation, source=source) as state:
            row = self.db.execute("SELECT * FROM attempts WHERE attempt_id=?", (attempt_id,)).fetchone()
            require(row is not None and row["generation"] == generation and row["source"] == source,
                    "worker belongs to an older source")
            require(row["status"] == "STARTED" and row["proposal"] == application["proposal_digest"],
                    "attempt/proposal identity differs")
            self.db.execute("INSERT INTO applications VALUES(?,?,?,?,?)",
                (app_id, attempt_id, generation, source, canonical_bytes(application)))
            event = self._event(state, "APPLICATION_VERIFIED", {"attempt_id": attempt_id,
                                "application_id": app_id, "evidence": application["evidence_digest"]})
            self.db.execute("UPDATE attempts SET status=?,evidence=? WHERE attempt_id=?",
                            ("PROVED_CONDITIONAL", application["evidence_digest"], attempt_id))
        return event

    def archive(self, payload: dict, *, expected_revision: int):
        """Late evidence may be retained, but cannot become a current application."""
        with self._transaction(expected_revision=expected_revision) as state:
            return self._event(state, "EVIDENCE_ARCHIVED", payload)

    def invalidate(self, reason: str, *, generation: str, source: str, expected_revision: int):
        nonempty_text(reason, "invalidation reason")
        with self._transaction(expected_revision=expected_revision, generation=generation, source=source) as state:
            event = self._event(state, "GENERATION_INVALIDATED", {"reason": reason})
            self.db.execute("UPDATE state SET generation=NULL,source=NULL,profile=NULL WHERE singleton=1")
        return event

    def verify_chain(self) -> dict:
        previous = ZERO; revision = 0; active = None; source = None; profile = None
        generations = set(); ids = set(); generation_rows = {}; menus = {}; attempts = {}; applications = {}
        for row in self.db.execute("SELECT * FROM events ORDER BY revision"):
            body = load_bytes(row["body"])
            require(body["revision"] == revision + 1 == row["revision"] and body["previous"] == previous,
                    "journal sequence or parent corrupted")
            require(body["event_id"] == row["event_id"] and body["event_id"] not in ids,
                    "journal event identity corrupted")
            require(digest(body, domain="OPICA_JOURNAL_EVENT_V2") == row["event_hash"], "journal hash corrupted")
            require(body["kind"] in KINDS, "unknown journal event kind")
            if body["kind"] == "GENERATION_STARTED":
                require(active is None and body["generation"] not in generations, "illegal generation lifecycle")
                active = body["generation"]; source = body["source"]; profile = body["payload"]["profile"]
                generations.add(active)
                generation_rows[active] = (active, source, profile)
            elif body["kind"] != "EVIDENCE_ARCHIVED":
                require(body["generation"] == active and body["source"] == source,
                        "stale journal event publication")
                if body["kind"] == "GENERATION_INVALIDATED": active = source = profile = None
            payload = body["payload"]
            if body["kind"] == "REVIEW_RECORDED" and payload.get("kind") == "MENU_FROZEN":
                require(body["generation"] not in menus, "menu was replaced inside generation")
                menus[body["generation"]] = payload["menu"]
            elif body["kind"] == "ATTEMPT_STARTED":
                aid = payload["attempt_id"]
                require(aid not in attempts and menus.get(body["generation"]) == payload["menu"],
                        "attempt menu or identity corrupted")
                attempts[aid] = {"attempt_id": aid, "generation": body["generation"],
                    "source": body["source"], "action_id": payload["action_id"],
                    "proposal": payload["proposal"], "start_revision": body["revision"],
                    "status": "STARTED", "evidence": None}
            elif body["kind"] in {"ADAPTER_REQUIRED", "APPLICATION_REJECTED", "RESOURCE_EXHAUSTED", "APPLICATION_VERIFIED"}:
                aid = payload["attempt_id"]
                require(aid in attempts and attempts[aid]["status"] == "STARTED", "outcome without live attempt")
                attempts[aid]["status"] = "PROVED_CONDITIONAL" if body["kind"] == "APPLICATION_VERIFIED" else payload["status"]
                if body["kind"] == "APPLICATION_VERIFIED":
                    attempts[aid]["evidence"] = payload["evidence"]
                    applications[payload["application_id"]] = (aid, body["generation"], body["source"], payload["evidence"])
            ids.add(body["event_id"]); previous = row["event_hash"]; revision += 1
        state = self.state()
        require((state["revision"], state["last_hash"], state["generation"], state["source"], state["profile"]) ==
                (revision, previous, active, source, profile), "journal state projection corrupted")
        require({r["generation"]: tuple(r) for r in self.db.execute("SELECT generation,source,profile FROM generations")} == generation_rows,
                "generation projection corrupted")
        actual_menus = {r["generation"]: r for r in self.db.execute("SELECT * FROM menus")}
        require(set(actual_menus) == set(menus), "menu projection corrupted")
        for generation, row in actual_menus.items():
            require(row["digest"] == menus[generation] == digest(load_bytes(row["body"]), domain="OPICA_MENU_V1"),
                    "menu body corrupted")
        require({r["attempt_id"]: dict(r) for r in self.db.execute("SELECT * FROM attempts")} == attempts,
                "attempt history projection corrupted")
        actual_apps = {r["application_id"]: r for r in self.db.execute("SELECT * FROM applications")}
        require(set(actual_apps) == set(applications), "application projection corrupted")
        for app_id, row in actual_apps.items():
            aid, gen, src, evidence = applications[app_id]
            value = load_bytes(row["body"])
            require((row["attempt_id"], row["generation"], row["source"]) == (aid, gen, src) and
                    digest(value, domain="OPICA_PUBLISHED_APPLICATION_V1") == app_id and
                    value["proposal_digest"] == attempts[aid]["proposal"] and
                    value["evidence_digest"] == evidence and value["source_generation"] == gen,
                    "published application body corrupted")
        return state

    def export_events(self) -> bytes:
        self.verify_chain()
        return b"".join(canonical_bytes({**load_bytes(r["body"]), "event_hash": r["event_hash"]}) + b"\n"
                        for r in self.db.execute("SELECT * FROM events ORDER BY revision"))

    def current_applications(self) -> list[dict]:
        state = self.verify_chain()
        if state["generation"] is None: return []
        return [load_bytes(r["body"]) for r in self.db.execute(
            "SELECT body FROM applications WHERE generation=? ORDER BY application_id", (state["generation"],))]

def publish_verified_application(journal: Journal, attempt_id: str, artifacts, snapshot, target, *,
                                 worker, generation: str, source: str, expected_revision: int):
    """The sole public positive publisher always performs independent native replay."""
    from .evidence import verify_application
    require(snapshot.generation == generation and snapshot.source_digest == source,
            "publisher snapshot differs from active mathematical world")
    check_output = journal.path.parent / "checks" / uuid.uuid4().hex
    verified = verify_application(artifacts, target, snapshot, check_output, worker=worker)
    record = verified.to_dict() if hasattr(verified, "to_dict") else verified
    require(worker.production is True, "development execution cannot publish a production proof")
    assure_application_gates(record, target, snapshot)
    return journal._publish(_PUBLISH, attempt_id, record, generation=generation,
                            source=source, expected_revision=expected_revision)

def assure_application_gates(record: dict, target, snapshot) -> None:
    """Reconstruct the admitted native gate set from actual independent output."""
    from .contracts import AttemptArtifacts
    from .evidence import validate_artifact_manifest
    from .executor import parse_native, generate_consumer
    from .inventory import expression_hash
    from .snapshot import check_snapshot, file_hash
    from research.RHRC.ffbbp.opica_composition import verify_required_gates
    names=('SOURCE','KERNEL','AXIOMS','INDEPENDENT_EXPECTED_TYPE')
    require(len(target.required_gates)==4 and set(target.required_gates)==set(names),
            'unknown, missing or duplicate application assurance gate')
    check_snapshot(snapshot)
    replay=AttemptArtifacts.from_dict(record['independent_replay']['replay'])
    root=validate_artifact_manifest(replay)
    native=parse_native(root/'OpicaConsumer.lean.log','OPICA_INDEPENDENT')
    require((root/'OpicaConsumer.lean').read_text(encoding='utf-8')==generate_consumer(target),
            'independent consumer recipe changed')
    consumer=record['independent_replay']['consumer']
    conditions={
        'SOURCE':replay.snapshot_digest==snapshot.digest and record['source_generation']==snapshot.generation,
        'KERNEL':replay.status=='PROVED_CONDITIONAL' and replay.native.get('exit_code')==0 and
            consumer.get('exit_code')==0 and consumer.get('resource_status') is None and
            consumer.get('capability')=='LINUX_ISOLATED' and (root/'OpicaConsumer.olean').is_file(),
        'AXIOMS':native['axioms']==record['axioms'] and set(native['axioms'])<=set(target.allowed_axioms) and
            not set(native['constants']) & set(target.forbidden_constants or []),
        'INDEPENDENT_EXPECTED_TYPE':expression_hash(native['type_expression'])==target.expected_type_hash and
            record['target_digest']==target.digest,
    }
    identity={'source':snapshot.source_digest,'generation':snapshot.generation,'target':target.digest}
    wanted=[{'id':name,'scope':'CURRENT_HOST','identity':identity,'checker':'OPICA_NATIVE_GATE_V1'} for name in names]
    evidence=file_hash(root/'OpicaConsumer.lean.log')
    got=[{**row,'status':'PASS' if conditions[row['id']] else 'FAIL','evidence':[evidence]} for row in wanted]
    verify_required_gates(wanted,got,lambda req,row:conditions[req['id']] is True and
        file_hash(root/'OpicaConsumer.lean.log')==row['evidence'][0])

def store_artifact(root: Path, logical_name: str, data: bytes, *, maximum_bytes=32 * 1024 * 1024) -> dict:
    """Writer-owned content store; candidate paths and links cannot choose a destination."""
    relative_path(logical_name)
    require(type(data) is bytes and len(data) <= maximum_bytes, "artifact size budget exceeded")
    root = Path(root).absolute(); _no_links(root)
    h = hashlib.sha256(data).hexdigest()
    folder = root/h; folder.mkdir(parents=True, exist_ok=True); _no_links(folder)
    path = folder/Path(logical_name).name
    if path.exists():
        require(not path.is_symlink() and path.read_bytes() == data, "content-store collision or mutation")
    else:
        flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0)
        fd = os.open(path, flags, 0o600)
        with os.fdopen(fd, "wb") as stream:
            stream.write(data); stream.flush(); os.fsync(stream.fileno())
    return {"path": f"{h}/{path.name}", "bytes": len(data), "sha256": h}

def replay_events(raw: bytes) -> list[dict]:
    rows = [load_bytes(line) for line in raw.splitlines() if line]
    previous = ZERO
    for revision, row in enumerate(rows, 1):
        body = {k: v for k, v in row.items() if k != "event_hash"}
        require(body["revision"] == revision and body["previous"] == previous, "invalid exported journal sequence")
        require(row["event_hash"] == digest(body, domain="OPICA_JOURNAL_EVENT_V2"), "invalid exported journal hash")
        previous = row["event_hash"]
    return rows

def require_revival(previous: dict, current: dict, evidence_digest: str) -> None:
    digest_text(evidence_digest)
    require(previous.get("blocker") and current.get("blocker") == previous["blocker"], "named prior blocker required")
    require(previous.get("premise_digest") != current.get("premise_digest"), "renaming is not changed premises")
    digest_text(current["premise_digest"])
