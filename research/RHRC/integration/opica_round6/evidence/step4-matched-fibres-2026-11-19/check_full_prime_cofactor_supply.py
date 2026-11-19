"""Integer lower-sum certificate for uniform two- and three-prime supply."""
import json
from pathlib import Path


def lower_sum(grid, low, high):
    units = 10**9
    total = 0
    semiprime_cells = 0
    triple_cells = 0
    for i in range(grid//100, grid//2):
        if 2*i + 3 < grid and max(grid-i, i+1) <= low:
            total += units*grid // ((i+1)*(grid-i))
            semiprime_cells += 1
        for j in range(i+1, (grid-i-4)//2):
            c = grid-i-j
            guaranteed_singles = sum(v <= low for v in (i+1, j+1, c))
            possible_pairs = sum(v <= high for v in (i+j, grid-j-2, grid-i-2))
            weight = guaranteed_singles - 1 - possible_pairs
            if weight > 0:
                total += units*weight*grid // ((i+1)*(j+1)*c)
                triple_cells += 1
    return total, semiprime_cells, triple_cells


def main():
    grid = 400
    records = []
    for low in range(120, grid, 2):
        total, pairs, triples = lower_sum(grid, low, low+2)
        records.append(dict(alpha_left_numerator=low,alpha_right_numerator=low+2,
                            units=total,semiprime_cells=pairs,triple_cells=triples))
    worst = min(records, key=lambda row: row['units'])
    assert worst['units'] > 1080000000
    result = {'grid':grid,'units_per_one':10**9,'minimum':worst,'all_bins':records,
              'scope':'Exact combinatorial lower Darboux sums. Uniform prime asymptotics use ordinary PNT separately.'}
    Path(__file__).with_name('FULL_PRIME_COFACTOR_SUPPLY.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(worst, 'bins',len(records))


if __name__ == '__main__':
    main()
