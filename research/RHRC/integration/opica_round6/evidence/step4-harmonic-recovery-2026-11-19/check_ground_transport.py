"""Ordered sign transport and optimal weighted-prefix recovery for the genuine first harmonic."""
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
from time import monotonic

import flint
from flint import arb, ctx, fmpz


def weight(n, q):
    return (arb(2*(n-q))/q).cos_pi()/(2*q*(arb(1)/q).sin_pi()**2)


def ball(value):
    result = value.str(28)
    assert arb(result).contains(value)
    return result


def run():
    t0 = monotonic()
    ctx.prec = 128
    L = 2**26
    n = 21*L//20
    H = int(fmpz(L**2).root(5))
    assert H**5 <= L**2 < (H+1)**5
    start = 24*L//25+1
    assert L+int(fmpz(L**5).root(6)) < n <= int(fmpz(L**101).root(100))
    assert start*2 > L and 9*start > 3*L
    ground = counts = history = matched = unmatched = arb(0)
    floor_cost2 = history_cost2 = count_cost2 = history_norm2 = arb(0)
    physical_pair_cost = physical_endpoint_cost = physical_prefix_cost = arb(0)
    positive = negative = delta_squared = 0
    labels_plus = labels_minus = 0
    pairdist = Counter()
    ghostdist = Counter()
    ghost_count = ghost_cost = pair_cost = prefix_cost = bins = 0
    max_delta = max_local_prefix = 0
    quarter = a_half = 0
    for left in range(start, L+1, H):
        right = min(left+H-1,L)
        atoms = []
        for q in range(left, right+1):
            if q%6 not in (1,5):
                continue
            sign = int(fmpz(q).moebius_mu())
            if not sign:
                continue
            v = weight(n,q)
            assert v > 0
            atoms.append((q,sign,v))
            ground += sign*v
        if not atoms:
            continue
        bins += 1
        plus = [i for i,(_,s,_) in enumerate(atoms) if s==1]
        minus = [i for i,(_,s,_) in enumerate(atoms) if s==-1]
        labels_plus += len(plus)
        labels_minus += len(minus)
        d = len(plus)-len(minus)
        delta_squared += d*d
        max_delta = max(max_delta,abs(d))
        positive += max(d,0)
        negative += max(-d,0)
        qlast, _, vlast = atoms[-1]
        counts += d*vlast
        count_cost2 += vlast**2
        avg = sum((v for _,_,v in atoms),arb(0))/len(atoms)
        floor_cost2 += sum(((v-avg)**2 for _,_,v in atoms),arb(0))
        pref = 0
        for (q,s,v),(nq,_,nv) in zip(atoms,atoms[1:]):
            pref += s
            dq, dv = nq-q, nv-v
            assert dv > 0
            history -= dv*pref
            prefix_cost += dq*abs(pref)
            physical_prefix_cost += dv*abs(pref)
            history_cost2 += dv**2/dq
            history_norm2 += dq*pref*pref
            max_local_prefix = max(max_local_prefix,abs(pref))
        max_local_prefix = max(max_local_prefix,abs(d))
        plus.extend([None]*max(-d,0))
        minus.extend([None]*max(d,0))
        for ip,im in zip(plus,minus):
            if ip is None or im is None:
                i = im if ip is None else ip
                q,s,v = atoms[i]
                unmatched += s*v
                dist = qlast-q
                ghost_count += 1
                ghostdist[dist] += 1
                ghost_cost += dist
                physical_endpoint_cost += abs(vlast-v)
            else:
                q,_,v = atoms[ip]
                r,_,w = atoms[im]
                matched += v-w
                dist = abs(q-r)
                pairdist[dist] += 1
                pair_cost += dist
                physical_pair_cost += abs(v-w)
                quarter += dist <= 25
                a_half += dist <= 100
    assert pair_cost+ghost_cost == prefix_cost
    assert (physical_pair_cost+physical_endpoint_cost).overlaps(physical_prefix_cost)
    assert ghost_count == positive+negative
    assert 2*sum(pairdist.values())+ghost_count == labels_plus+labels_minus
    assert (counts+history).overlaps(ground)
    assert (matched+unmatched).overlaps(ground)
    assert (unmatched-counts+matched).overlaps(history)
    prior = Path(__file__).resolve().parents[1]/"step4-native-residual-2026-11-19"/"ONE_HARMONIC_CHECK.json"
    old = json.loads(prior.read_bytes())
    assert old["cutoff_L"]==L and arb(old["signed_row_direct_order"]).overlaps(ground)
    assert (labels_plus,labels_minus)==(old["eligible_mu_plus_one"],old["eligible_mu_minus_one"])
    def quantiles(counter):
        thresholds = [50,90,99,100]
        total, running, qtiles = sum(counter.values()), 0, {}
        for x,c in sorted(counter.items()):
            running += c
            while thresholds and running*100 >= total*thresholds[0]:
                qtiles[str(thresholds.pop(0))] = x
        return qtiles
    output = dict(scope="Finite true-row verification on one cutoff",L=L,n=n,first_q=start,last_q=L,
        block_width=H,nonempty_bins=bins,labels_plus=labels_plus,labels_minus=labels_minus,
        plus_unmatched=positive,minus_unmatched=negative,unmatched_labels=ghost_count,real_pairs=sum(pairdist.values()),
        real_pair_distance_quantiles=quantiles(pairdist),unmatched_to_cell_endpoint_distance_quantiles=quantiles(ghostdist),
        real_pairs_at_distance_le_25=quarter,real_pairs_at_distance_le_100=a_half,
        integer_distance_real_pairs=pair_cost,integer_distance_endpoint_corrections=ghost_cost,
        exact_integer_transport_cost=prefix_cost, sum_squares_cell_imbalances=delta_squared,
        physical_absolute_difference_real_pairs=ball(physical_pair_cost),
        physical_absolute_difference_endpoints=ball(physical_endpoint_cost),
        physical_optimal_absolute_transport_from_prefixes=ball(physical_prefix_cost),
        maximum_cell_end_imbalance=max_delta,maximum_absolute_active_prefix=max_local_prefix,
        signed_true_row=ball(ground),signed_real_matched_rows=ball(matched),
        signed_remaining_real_rows=ball(unmatched),signed_endpoint_cell_counts=ball(counts),
        signed_prefix_history=ball(history),count_only_minimax_unit_l2_error=ball(floor_cost2.sqrt()),
        count_channel_recovery_norm=ball(count_cost2.sqrt()),weighted_history_channel_recovery_norm=ball(history_cost2.sqrt()),
        combined_optimal_recovery_norm=ball((count_cost2+history_cost2).sqrt()),
        actual_weighted_history_norm=ball(history_norm2.sqrt()),
        prior_row_check_sha256=sha256(prior.read_bytes()).hexdigest(),arb_precision_bits=ctx.prec,
        python_flint_version=flint.__version__,source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        seconds=round(monotonic()-t0,2))
    Path(__file__).with_name("GROUND_TRANSPORT_CHECK.json").write_text(json.dumps(output,indent=2)+"\n",encoding="utf8")
    print(json.dumps(output,indent=2))


if __name__ == "__main__":
    run()
