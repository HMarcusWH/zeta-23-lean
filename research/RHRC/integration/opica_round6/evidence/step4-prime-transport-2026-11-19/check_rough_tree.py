"""Exact finite Euler-pattern restrictions on the published, shared native dyadic tree."""
from collections import Counter
from fractions import Fraction
from hashlib import sha256
import importlib.util
import json
from pathlib import Path

import flint
from flint import fmpz


here=Path(__file__).resolve()
supplier_path=here.parents[1]/"step4-harmonic-recovery-2026-11-19"/"check_dyadic_tree.py"
spec=importlib.util.spec_from_file_location("native_dyadic_tree",supplier_path)
native=importlib.util.module_from_spec(spec)
spec.loader.exec_module(native)


def run_case(x):
    first,cap,top,s,shells,_,digest=native.native_input(x)
    y=(x-1).bit_length()**2
    shift=top+max(0,top-s)
    pools={key:{j:[] for j in shells} for key in ("rough","nonrough","exact_pattern_5")}
    signs={key:Counter() for key in pools}
    prime_degrees=Counter()
    for j,labels in shells.items():
        for q,v,ds in labels:
            facts=list(fmpz(q).factor())
            assert all(e==1 for p,e in facts)
            a=1
            for p,_ in facts:
                if p<=y:
                    a*=int(p)
            kind="rough" if a==1 else "nonrough"
            if a==1:
                prime_degrees[str(len(facts))]+=1
            entry=(q,v,ds)
            pools[kind][j].append(entry)
            signs[kind][str(v)]+=1
            if a==5:
                assert int(fmpz(q//5).moebius_mu())==-v
                pools["exact_pattern_5"][j].append(entry)
                signs["exact_pattern_5"][str(v)]+=1
    results={}
    for name,pool in [("full",shells),*pools.items()]:
        nums,_=native.tree_covariance(pool,s,shift,cap)
        if x<10000:
            true_native=native.direct_pairs(pool,s,shift,cap)
            assert nums==true_native
        results[name]=nums
    full=results["full"]
    mixed={k:n-results["rough"][k]-results["nonrough"][k] for k,n in full.items()}
    assert mixed["diagonal"]==0
    assert cap<5 and results["exact_pattern_5"]["strict_small_gcd_off_diagonal"]==0
    results["mixed_rough_nonrough"]=mixed
    return dict(X=x,y=y,first_terminal=first,native_gcd_cap=cap,sign_counts=signs,
        rough_label_prime_factor_count=prime_degrees,
        full_mu6_digest=digest,direct_ordered_weight_reconstruction_all_sectors=x<10000,
        results={kind:{key:str(Fraction(val,1<<shift)) for key,val in measures.items()}
                 for kind,measures in results.items()})


if __name__=="__main__":
    data=dict(status="FINITE_EULER_PATTERN_TREE_EVALUATION",cases=[run_case(4103),run_case(2**20)],
        kernel="Published dyadic ascending-pair incidence, includes all complementary nodes and exact GCD cutoff.",
        pattern="y=(ceil(log2 X))^2, rough iff no prime <=y divides q; exact_pattern_5 means gcd(q,product_{p<=y}p)=5.",
        note="For these cutoffs X<=5^100 every pair in the nonempty fixed-pattern-5 sector fails the strict native gcd cutoff. Its asymptotic result begins beyond the cutoff-dependent threshold.",
        flint=flint.__version__,source_sha256=sha256(here.read_bytes()).hexdigest(),
        native_tree_verifier_sha256=sha256(supplier_path.read_bytes()).hexdigest())
    here.with_name("ROUGH_TREE_CHECK.json").write_text(json.dumps(data,indent=2)+"\n",encoding="utf8")
    for row in data["cases"]:
        print(row["X"],row["y"],row["sign_counts"],row["rough_label_prime_factor_count"],
              [(kind,vals["strict_small_gcd_off_diagonal"]) for kind,vals in row["results"].items()])
