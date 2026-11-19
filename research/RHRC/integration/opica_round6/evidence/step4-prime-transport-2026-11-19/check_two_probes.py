"""Exact full-tree Gram and independent weighted squared minors for two actual probes."""
from array import array
from bisect import bisect_left
from collections import Counter, defaultdict
from fractions import Fraction
from hashlib import sha256
from itertools import combinations
from math import isqrt
from pathlib import Path
import json


X = 2**20
PAIRS = ((0, 1), (0, 2), (1, 2))
PAIR_NAMES = ("P_F", "A_F", "P_A")


def make_labels():
    y = (X - 1).bit_length()**2
    low, high = 0, X
    threshold = X**99
    while high - low > 1:
        mid = (low + high) // 2
        if mid**100 <= threshold:
            low = mid
        else:
            high = mid
    first = high
    assert (first - 1)**100 <= threshold < first**100
    assert 1**1000 <= X < 2**1000
    least = array("I", range(X + 1))
    for p in range(2, isqrt(X) + 1):
        if least[p] != p:
            continue
        for n in range(p*p, X+1, p):
            if least[n] == n:
                least[n] = p
    values = {}
    for n in range(first, X+1):
        if least[n] <= y:
            continue
        co = n
        factors = []
        while co > 1:
            p = least[co]
            co //= p
            if co % p == 0:
                break
            factors.append(p)
        else:
            sign = (-1)**len(factors)
            values[n] = (sign, sign if len(factors) == 1 else 0,
                         sign if n // factors[-1] <= 512 else 0)
    return first, y, values


def evaluate(first, data, native):
    top = X.bit_length() - 1
    s = 1 + isqrt(top-1)
    shift = top + max(0, top-s)
    denom = 1 << shift
    labels = sorted(data)
    emit = {n: ((v[0], v[1], v[1]) if native else v) for n, v in data.items()}
    prefix = [[0] for _ in range(3)]
    for n in labels:
        for i in range(3):
            prefix[i].append(prefix[i][-1] + emit[n][i])
    sums = {}
    for n, row in emit.items():
        j = n.bit_length() - 1
        depth = max(0, j-s)
        for k in range(depth+1):
            key = (j, k, n >> (depth-k))
            acc = sums.setdefault(key, [0, 0, 0])
            for i in range(3):
                acc[i] += row[i]

    matrix = [[0]*3 for _ in range(3)]
    groups = Counter()
    depth_data = {}
    shell_info = []
    sample_candidates = []
    # Cover even clipped and zero-charge nodes by iterating over every intersecting node.
    for j in range(first.bit_length()-1, top+1):
        lo, hi = max(first, 1 << j), min(X+1, 1 << (j+1))
        if lo >= hi:
            continue
        depth = max(0, j-s)
        left, right = bisect_left(labels,lo), bisect_left(labels,hi)
        charges = [pr[right]-pr[left] for pr in prefix]
        node_count = 0
        for k in range(depth+1):
            width = 1 << (depth-k)
            weight = 1 << (shift-j-k)
            class_weights = Counter()
            for index in range(lo//width, (hi-1)//width+1):
                l = bisect_left(labels, max(lo,index*width))
                r = bisect_left(labels, min(hi,(index+1)*width))
                vec = tuple(pr[r]-pr[l] for pr in prefix)
                assert vec == tuple(sums.get((j,k,index), (0,0,0)))
                node_count += 1
                groups[vec] += weight
                class_weights[vec] += weight
                for a in range(3):
                    for b in range(a,3):
                        matrix[a][b] += weight*vec[a]*vec[b]
                if k <= 1:
                    sample_candidates.append(((j,k,index),weight,vec))
            depth_data[j,k] = (1 << depth, width, weight, class_weights)
        shell_info.append({"U":1 << j, "observed_range":[lo,hi-1], "charges_F_P_A":charges,
                           "intersecting_nodes":node_count,
                           "shell_ratio_A_over_P": str(Fraction(charges[2],charges[1])) if charges[1] else None})
    for a,b in PAIRS:
        matrix[b][a] = matrix[a][b]
    determinants = [matrix[a][a]*matrix[b][b]-matrix[a][b]**2 for a,b in PAIRS]

    # A node pair has identical weighted minor to every other pair with the same
    # two integer charge triples, up to the two scalar weights. Equal triples give zero.
    direct = [0]*3
    for (v, weight_v),(u,weight_u) in combinations(groups.items(), 2):
        ww = weight_v*weight_u
        for i,(a,b) in enumerate(PAIRS):
            direct[i] += ww*(v[a]*u[b]-v[b]*u[a])**2
    assert direct == determinants
    # The decision uses the underlying grid lengths even at clipped terminal
    # endpoints. Enumerate *all* pairs of shell/depth blocks, including themselves.
    depth_grams = {}
    for key, (_,_,weight,values) in depth_data.items():
        g = [[sum(w*v[i]*v[j] for v,w in values.items()) for j in range(3)] for i in range(3)]
        depth_grams[key] = (g, sum(values.values()) // weight)
    part = {label:dict(count=0, block_pairs=0, minor=[0,0,0], by_classes=[0,0,0])
            for label in ("cheap","remaining")}
    block_keys = sorted(depth_data)
    for i, first_key in enumerate(block_keys):
        h0,h,_,v_dict = depth_data[first_key]
        gv,nv = depth_grams[first_key]
        for second_key in block_keys[i:]:
            d0,d,_,u_dict = depth_data[second_key]
            gu,nu = depth_grams[second_key]
            same = first_key == second_key
            section = part["cheap" if h*h*d*d <= X*h0*d0 else "remaining"]
            section["count"] += nv*(nv-1)//2 if same else nv*nu
            section["block_pairs"] += 1
            for ip,(a,b) in enumerate(PAIRS):
                if same:
                    subtotal = gv[a][a]*gv[b][b]-gv[a][b]**2
                else:
                    subtotal = gv[a][a]*gu[b][b]+gv[b][b]*gu[a][a]-2*gv[a][b]*gu[a][b]
                assert subtotal >= 0
                section["minor"][ip] += subtotal
            if same:
                classes = combinations(v_dict.items(), 2)
            else:
                classes = ((v,u) for v in v_dict.items() for u in u_dict.items())
            for (v,wv),(u,wu) in classes:
                for ip,(a,b) in enumerate(PAIRS):
                    section["by_classes"][ip] += wv*wu*(v[a]*u[b]-v[b]*u[a])**2
    for section in part.values():
        assert section["minor"] == section["by_classes"]
    assert all(part["cheap"]["minor"][ip]+part["remaining"]["minor"][ip] == determinants[ip]
               for ip in range(3))
    total_nodes = sum(item["intersecting_nodes"] for item in shell_info)
    assert sum(section["count"] for section in part.values()) == total_nodes*(total_nodes-1)//2
    area_sectors = {}
    for label,section in part.items():
        vals = section["minor"]
        area_sectors[label] = dict(
            unordered_distinct_node_pairs=section["count"],
            unordered_shell_depth_block_pairs_including_self=section["block_pairs"],
            squared_wedges={name:str(Fraction(v,denom**2)) for name,v in zip(PAIR_NAMES,vals)},
            two_probe_angular_sum=str(Fraction(vals[0]+vals[1],denom**2)),
            fraction_of_single_prime_full_D=str(Fraction(vals[0],direct[0])),
            fraction_of_two_probe_full_angular_sum=str(Fraction(vals[0]+vals[1],direct[0]+direct[1])))
    samples = []
    for (nj,wj,v),(nk,wk,u) in combinations(sample_candidates,2):
        raw = [v[a]*u[b]-v[b]*u[a] for a,b in PAIRS]
        if any(raw) and len(samples)<3:
            samples.append({"nodes":[nj,nk], "charges_F_P_A":[v,u],
                            "signed_minors_FxP_FxA_PxA":raw,
                            "weighted_squared_minors_PF_AF_PA":[str(Fraction(wj*wk*r*r,denom**2)) for r in raw]})
    ff, trace = matrix[0][0], matrix[1][1]+matrix[2][2]
    angular = direct[0]+direct[1]
    assert trace*angular >= ff*direct[2]
    assert (direct[2] == 0) == native
    return {"threshold": "floor(X^(1/1000))=1" if native else "512 (auxiliary)",
            "full_prime_cone_label_counts":[sum(bool(row[i]) for row in emit.values()) for i in range(3)],
            "grid":{"s":s,"common_weight_denominator":denom,"charge_classes":len(groups),
                    "intersecting_nodes":sum(r["intersecting_nodes"] for r in shell_info),"shells":shell_info},
            "gram_order":["F","P","A"],
            "gram":[[str(Fraction(value,denom)) for value in row] for row in matrix],
            "squared_wedges":{name:str(Fraction(value,denom**2)) for name,value in zip(PAIR_NAMES,direct)},
            "two_probe_angular_sum":str(Fraction(angular,denom**2)),
            "native_area_partition":{"cheap_criterion":"H_I^2 H_J^2 <= X H0_I H0_J at the actual underlying dyadic levels",
                                     "crosscheck":"All weighted minors regrouped and summed independently by direct charge triples and shell/depth Gram products. All pieces nonnegative; all node-pair counts and total areas verified.",
                                     "sectors":area_sectors},
            "squared_P_A_sine":str(Fraction(direct[2],matrix[1][1]*matrix[2][2])),
            "lower_observability_coefficient_det_P_A_over_trace":str(Fraction(direct[2],denom*trace)),
            "observed_angular_sum_over_F_norm_squared":str(Fraction(angular,denom*ff)),
            "trace_times_angular_minus_F_norm_squared_times_P_A_area":str(Fraction(trace*angular-ff*direct[2],denom**3)),
            "all_node_pair_minor_check":"Exact direct sum grouped by distinct integer charge triples, including clipped nodes. Each minor sum equals its Gram determinant.",
            "node_charge_crosscheck":"Every node charge verified by independent sorted-label prefix differences and by ancestor accumulation.",
            "examples":samples}


if __name__ == "__main__":
    first,y,vals=make_labels()
    result={"X":X,"roughness":y,"first":first,"labels":"actual squarefree y-rough signed F, prime-only signed P, and signed squarefree cone A restricted by n/P+(n)",
            "scope":"Positive weighted full-node form before any diagonal or GCD subtraction. This X has a clipped shell and no whole terminal shell, so no two-shell asymptotic test is claimed.",
            "cases":[evaluate(first,vals,True),evaluate(first,vals,False)],
            "script_sha256":sha256(Path(__file__).read_bytes()).hexdigest()}
    Path(__file__).with_name("TWO_PROBE_CHECK.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf8")
    for case in result["cases"]:
        print(case["threshold"],case["two_probe_angular_sum"],case["squared_wedges"]["P_A"])
