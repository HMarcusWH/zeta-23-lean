"""Compiler statement inventory, preserving exact DAG hashes and memberships."""
from __future__ import annotations
import hashlib, json
from pathlib import Path
from collections import Counter
from .canonical import require, load_bytes
from .contracts import StatementContract, StatementInventory, CoverageReport, CohortInventory
from .snapshot import check_snapshot, file_hash
from research.RHRC.routes.R003_ccm_bridge.post290.lean_expr_dag import validate_expression

def expression_hash(expr):
    # This is the existing STRICT_CANONICAL_JSON_SORTED_KEYS_UTF8_V1 codec.
    raw=json.dumps(expr,ensure_ascii=False,sort_keys=True,separators=(",",":"),allow_nan=False).encode("utf-8")
    validate_expression(raw.decode("utf-8"))
    return hashlib.sha256(raw).hexdigest()

def validate_telescope(expression,binders):
    require(type(binders)is list,"ordered telescope required")
    nodes=expression["nodes"]; current=int(expression["root"]); actual=[]
    while True:
        node=nodes[current]
        if node[0]=="mdata": current=int(node[2]); continue
        if node[0]!="forall": break
        actual.append(node[2]); current=int(node[4])
    require(len(binders)==len(actual),"outer telescope dropped a binder")
    keys={"position","name","binder_info","domain_text","domain_is_prop","typeclass_binder","class_name"}
    for index,(binder,info) in enumerate(zip(binders,actual)):
        require(type(binder)is dict and set(binder)==keys,"closed binder record required")
        require(type(binder["position"])is int and binder["position"]==index and binder["binder_info"]==info,
                "binder slot/order/info differs from full DAG")
        require(type(binder["domain_is_prop"])is bool and type(binder["typeclass_binder"])is bool and
                binder["typeclass_binder"] is (info=="instImplicit"),"binder proposition/typeclass role differs")
        require(type(binder["name"])is str and type(binder["domain_text"])is str and binder["domain_text"] and
                (binder["class_name"] is None or type(binder["class_name"])is str),"binder metadata malformed")

def load_statement_inventory(snapshot,native_export):
    snapshot=check_snapshot(snapshot); path=Path(native_export)
    rows=[]
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.startswith("OPICA3_ATLAS\t"): continue
        row=load_bytes(line.split("\t",1)[1].encode("utf-8"))
        required={"schema","declaration","module","kind","universe_parameters","type_text","type_expression",
                  "outer_telescope","conclusion_text","type_constants","value_constants","structure_constants","axioms"}
        require(set(row)==required and row["schema"]=="OPICA3_ATLAS_COMPILER_ROW_V1","native inventory row differs")
        expression_hash(row["type_expression"])
        validate_telescope(row["type_expression"],row["outer_telescope"])
        require(row["kind"] in {"THEOREM","DEFINITION","OPAQUE","INDUCTIVE","CONSTRUCTOR","RECURSOR"},"axiom source provider refused")
        require(set(row["axioms"])<={"propext","Classical.choice","Quot.sound"},"unapproved inventory axiom")
        contract=StatementContract(**{k:row[k] for k in ("declaration","module","type_expression","universe_parameters",
                    "outer_telescope","conclusion_text","type_constants","value_constants","axioms")},
                    type_sha256=expression_hash(row["type_expression"]))
        record=contract.to_dict()
        # Memberships are independently frozen registration facts, while the
        # statement/type/telescope still come from the actual compiler row.
        membership_table=snapshot.environment.get("cohort_memberships",{})
        if membership_table:
            require(type(membership_table)is dict and row["declaration"] in membership_table,
                    "compiler declaration missing frozen cohort membership")
            record["memberships"]=membership_table[row["declaration"]]
        rows.append(record)
    require(rows and len({r["declaration"] for r in rows})==len(rows),"empty/duplicate compiler inventory")
    check_snapshot(snapshot)
    # Inventory is a semantic product: relocate identical source/environment
    # without changing its mathematical identity. Attempt artifacts separately
    # bind the full execution SnapshotIdentity (including native repo path).
    return StatementInventory(snapshot.generation,sorted(rows,key=lambda r:r["declaration"]),file_hash(path))

def check_membership_coverage(inventory,expected):
    if isinstance(expected,CohortInventory) and expected.memberships is not None:
        def key(row):
            require(type(row)is dict and set(row)=={"cohort","root_id","declaration"},"closed cohort membership required")
            require(all(type(v)is str and v for v in row.values()),"nonempty membership identities required")
            return json.dumps([row[k] for k in ("cohort","root_id","declaration")],ensure_ascii=False,separators=(",",":"))
        wanted=[key(row) for row in expected.memberships]
        actual=[]
        for row in inventory.statements:
            for member in row.get("memberships",[]):
                require(member.get("declaration")==row["declaration"],"membership declaration differs from compiler row")
                actual.append(key(member))
        counts=Counter(actual); dup=sorted(k for k,n in counts.items() if n>1)
        missing=sorted(set(wanted)-set(actual)); unexpected=sorted(set(actual)-set(wanted))
        declarations=[r["declaration"] for r in inventory.statements]
        population_ok=set(declarations)==set(expected.declarations) and len(set(declarations))==len(declarations)
        return CoverageReport(population_ok and not(missing or unexpected or dup or len(set(wanted))!=len(wanted)),missing,unexpected,dup)
    wanted=expected.declarations if isinstance(expected,CohortInventory) else list(expected)
    # Memberships may be qualified cohort:declaration IDs. They are not deduplicated by declaration.
    actual=[r.get("membership_id",r["declaration"]) for r in inventory.statements]
    dup=sorted(k for k,v in Counter(actual).items() if v>1)
    missing=sorted(set(wanted)-set(actual)); unexpected=sorted(set(actual)-set(wanted))
    return CoverageReport(not(missing or unexpected or dup or len(set(wanted))!=len(wanted)),missing,unexpected,dup)

def contact_disposition(contact):
    require(type(contact)is dict,"contact record required")
    status=contact.get("review_status",contact.get("status","UNREVIEWED"))
    require(type(status)is str and bool(status),"closed historical disposition required")
    return status
