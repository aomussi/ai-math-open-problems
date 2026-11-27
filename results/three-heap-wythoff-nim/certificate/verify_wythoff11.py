#!/usr/bin/env python3
"""Finite certificate for the m=11 Fraenkel three-heap Wythoff result.

Run with Python 3.10+ (standard library only):
    python verify_wythoff11.py

This script does NOT infer an infinite statement from a long numerical run.
It checks finite hypotheses used by the mathematical proof in the answer:
  1. exact game enumeration (all last-heap sizes, middle heap <= 5254);
  2. the stated initial 29 pairs and the finite part of the recurrence;
  3. 640 periodic legal-move witnesses excluding all 40 missing differences;
  4. the hypotheses of Sun--Zeilberger (2004), Lemma 2.6;
  5. strict separation from the previously proved slices m=0,...,10.

The infinite implications of Lemma 2.6 and the published lower-slice theorem
are mathematical dependencies, not claims to be formally checked here.
Paper: https://sites.math.rutgers.edu/~zeilberg/mamarimY/Zeilberger_y2004_p225.pdf
All heap coordinates are ACTUAL stone counts. All arithmetic is integral.

Writes reproducible CSV/JSON certificates to the selected output directory.
"""
import argparse
import csv
from itertools import permutations
import json
from math import isqrt
from pathlib import Path
import time

SEED_PAIRS = [
    (11,17), (13,29), (14,40), (15,19), (16,45), (20,52),
    (21,54), (23,60), (25,64), (26,66), (27,38), (30,75),
    (31,77), (33,81), (35,84), (36,86), (37,88), (39,92),
    (41,95), (42,98), (43,100), (44,102), (46,106), (47,108),
    (48,110), (49,112), (50,114), (51,116), (53,119),
]
EXCLUDED_ENDPOINTS = {12,18,22,24,28,32,34}
F = set(range(11)) | EXCLUDED_ENDPOINTS
D, ALPHA, START_ORDINAL = 1253, -61, 1214
LOWER_ALPHA = [0,-4,-10,-16,-20,-26,-32,-39,-46,-52,-56]
# Table 1 uses ordinals here, not the difference-index d.
LOWER_N2 = [1,28,58,73,208,123,232,343,648,645,656]
LOWER_PREFIX_MAX_GAP = [0,30,63,83,220,139,252,368,676,677,691]


def phi_floor(n):
    """Exactly floor(n*(1+sqrt(5))/2), for n >= 0."""
    return (n + isqrt(5*n*n)) // 2


def exact_slices(maximum_middle, maximum_minimum=11):
    """Exact P positions for every median <= maximum_middle; no b cutoff.

    Process min=m increasingly, and then median=a increasingly.  For a
    lower P position, consider EVERY permutation (q,r,s) with q<=m.  Its
    XOR predecessors satisfy
        b = s + ((m-q) xor (a-r)),  a>=r.
    Their difference b-a depends only on a modulo 2**m.bit_length().
    Activate this periodic forbidden-difference ray when a reaches r.

    Single-pile moves are covered by occupied endpoints and by single[a].
    In the current slice, equal removal from the two larger heaps forbids
    each previously used difference.  The first unblocked b is the unique
    P completion of an available median a; all greater b can move to it.
    Python integers encode unbounded finite sets as bit sets.
    """
    result = []
    for m in range(maximum_minimum + 1):
        period = 1 << m.bit_length()
        events = [[] for _ in range(maximum_middle + 1)]
        single = [0] * (maximum_middle + 1)
        excluded = set(range(m))
        for i, pairs in enumerate(result):
            for x,y in pairs:
                if x == m:
                    excluded.add(y)
                if m <= x <= maximum_middle:
                    single[x] |= 1 << (y-x)
                for q,r,s in set(permutations((i,x,y))):
                    if q <= m and r <= maximum_middle:
                        events[max(m,r)].append((q,r,s))
        occupied = sum(1 << t for t in excluded)
        used_differences = 0
        active = [0] * period
        pairs = []
        for a in range(m,maximum_middle + 1):
            for q,r,s in events[a]:
                u = m-q
                for residue in range(period):
                    v0 = (residue-r) % period
                    d = s-r + (u ^ v0) - v0
                    if d >= 0:
                        active[residue] |= 1 << d
            if occupied & (1 << a):
                continue
            forbidden = ((occupied >> a) | used_differences
                         | active[a % period] | single[a])
            d = ((~forbidden) & (forbidden+1)).bit_length()-1
            b = a+d
            pairs.append((a,b))
            occupied |= (1 << a) | (1 << b)
            used_differences |= 1 << d
        result.append(pairs)
    return result


def compact_sequence(number_of_pairs):
    occupied = set(F)
    pairs = []
    a = 0
    for n in range(1,number_of_pairs + 1):
        while a in occupied:
            a += 1
        if n <= 29:
            x,y = SEED_PAIRS[n-1]
            assert a == x
            d = y-x
        elif n < START_ORDINAL:
            d = n+38
        else:
            d = n+39
        b = a+d
        assert b not in occupied and b > a
        pairs.append((a,b))
        occupied.update((a,b))
    return pairs


def gap_witnesses(data, missing):
    """One lower P target for each (missing difference, median mod 16)."""
    witness = {}
    for i,pairs in enumerate(data[:11]):
        for x,y in pairs:
            for q,r,s in sorted(set(permutations((i,x,y)))):
                if q > 11:
                    continue
                u = 11-q
                for residue in range(16):
                    t = (residue-r) % 16
                    d = s-r+(u ^ t)-t
                    if d not in missing:
                        continue
                    start = max(11,r)
                    first_a = start+(residue-start) % 16
                    candidate = (first_a,i,x,y,q,r,s)
                    key = (d,residue)
                    if key not in witness or candidate < witness[key]:
                        witness[key] = candidate
    assert len(witness) == len(missing)*16
    lower_sets = [set(pairs) for pairs in data[:11]]
    for (d,residue), (a,i,x,y,q,r,s) in witness.items():
        assert (x,y) in lower_sets[i]
        assert sorted((q,r,s)) == [i,x,y]
        assert a >= 11 and a % 16 == residue
        u,v,w = 11-q,a-r,a+d-s
        assert min(u,v,w) >= 0 and u+v+w > 0 and (u ^ v ^ w) == 0
        assert u < 16 and v//16 == w//16
        # Since v and w have identical high parts and u<16, adding 16*k
        # to both v,w preserves their XOR, for EVERY integer k>=0.
    cutoffs = {
        d: max(11,1+max(witness[d,r][0]-16 for r in range(16)))
        for d in missing
    }
    return witness,cutoffs


def write_csv(path,header,rows):
    with path.open('w',newline='',encoding='utf-8') as stream:
        writer = csv.writer(stream)
        writer.writerow(header)
        writer.writerows(rows)


def verify(output):
    started = time.time()
    MAX_A = 5254
    data = exact_slices(MAX_A)
    p11 = data[11]
    assert len(p11) == 3246 and p11[-1] == (5254,8539)
    assert p11 == compact_sequence(len(p11))
    assert p11[:29] == SEED_PAIRS
    e = {y for pairs in data[:11] for x,y in pairs if x == 11}
    assert e == EXCLUDED_ENDPOINTS
    prefix = p11[:1213]
    assert prefix[-1] == (1965,3216)
    assert p11[1213:1216] == [(1967,3220),(1968,3222),(1970,3225)]
    T = F | {z for x,y in prefix for z in (x,y)}
    assert len(T) == 2444 and max(T) == 3216

    # Define a virtual Wythoff sequence, independently of the game tail.
    occupied = set(T)
    A,B,eps = {},{},{}
    a = 0
    for d in range(D,3286):
        while a in occupied:
            a += 1
        b = a+d
        assert b not in occupied and b > max(T)
        A[d],B[d],eps[d] = a,b,a-phi_floor(d)-ALPHA
        occupied.update((a,b))
    assert [(A[d],B[d]) for d in range(D,3286)] == p11[1213:]
    assert all(abs(eps[d]) <= 1 for d in range(D,3286))
    N,m1,m2 = 2026,2030,3285
    assert (A[N],A[m1],B[m1],A[m2],B[m2]) == (3217,3223,5253,5254,8539)
    assert A[N] > max(T) and N+2 < m1 < m2 and A[m2] > B[m1]
    assert all(abs(eps[d]) <= 1 for d in range(m1-4,m2+1))
    assert all(eps[d-2]*eps[d-1]*eps[d] == 0
               for d in range(m1-2,m2+1))

    missing = set(range(D)) - {y-x for x,y in prefix}
    expected_missing = {
        0,1,2,3,5,7,8,9,10,12,13,14,15,17,18,19,20,21,22,23,24,25,
        27,28,30,31,34,35,36,38,41,42,43,44,47,52,55,59,67,1252,
    }
    assert missing == expected_missing
    witness,cutoffs = gap_witnesses(data,missing)
    assert max(cutoffs.values()) == 1969
    assert max(cutoffs[d] for d in missing if d != 1252) == 65
    assert all(y-x not in missing for x,y in p11 if x <= 1968)
    # Thus EVERY a>=11 is covered by finite enumeration or a periodic ray.

    # Translate the lower-slice theorem's ordinal cutoff into difference bounds.
    observed_max = [max(y-x for x,y in data[i][:LOWER_N2[i]])
                    for i in range(11)]
    assert observed_max == LOWER_PREFIX_MAX_GAP
    assert D-11 > max(observed_max)
    margin = []
    for i,alpha in enumerate(LOWER_ALPHA):
        r = 11-i
        ceil_r_phi = phi_floor(r)+1
        margin.append(alpha+61-2-ceil_r_phi)
        assert margin[-1] > 0
        # A finite consistency check of the interpretation of Table 1.
        assert all(abs(x-phi_floor(y-x)-alpha) <= 1
                   for x,y in data[i][LOWER_N2[i]:])

    summary = {
        'result': 'All finite certificate checks passed.',
        'mathematical_dependencies': [
            'Sun--Zeilberger (2004), Lemma 2.6 (including the bound proved there)',
            'Sun--Zeilberger (2004), proved lower slices m=0,...,10, Table 1',
            'Exact-enumeration and infinite-induction arguments in the answer',
        ],
        'all_coordinates_are_actual_heap_sizes': True,
        'exact_enumeration': {
            'minimum_heap': [0,11], 'middle_heap_max': MAX_A,
            'last_heap': 'unbounded; exact first permitted completion of each median',
            'number_of_P_positions_per_slice': [len(p) for p in data],
        },
        'first_final_tail_ordinal': START_ORDINAL,
        'D': D, 'alpha': ALPHA,
        'ordinal_to_difference': {'30..1213': 'd=n+38', '1214..infinity': 'd=n+39'},
        'T_size': len(T), 'T_max': max(T),
        'lemma_2_6': {'N':N,'m1':m1,'m2':m2,'A_N':A[N],
                      'A_m1':A[m1],'B_m1':B[m1],'A_m2':A[m2],'B_m2':B[m2]},
        'missing_differences': sorted(missing),
        'missing_difference_uniform_a_cutoff': max(cutoffs.values()),
        'missing_difference_a_cutoffs': cutoffs,
        'periodic_witness_count': len(witness),
        'lower_prefix_max_differences': observed_max,
        'strict_separation_margins': margin,
    }
    output.mkdir(parents=True,exist_ok=True)
    write_csv(output/'wythoff11_prefix.csv', ['n','minimum','a','b','d'],
              ((n,11,x,y,y-x) for n,(x,y) in enumerate(prefix,1)))
    write_csv(output/'wythoff11_finite_check.csv', ['n','minimum','a','b','d'],
              ((n,11,x,y,y-x) for n,(x,y) in enumerate(p11,1)))
    write_csv(output/'wythoff11_gap_witnesses.csv',
              ['d','a_mod_16','first_a','target_min','target_mid','target_max',
               'ordered_q','ordered_r','ordered_s','u','v','w'],
              ((d,res,a,i,x,y,q,r,s,11-q,a-r,a+d-s)
               for (d,res),(a,i,x,y,q,r,s) in sorted(witness.items())))
    (output/'wythoff11_certificate.json').write_text(
        json.dumps(summary,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print(json.dumps(summary,indent=2,ensure_ascii=False))
    print(f'Elapsed: {time.time()-started:.2f} seconds')
    return summary


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O: this verifier uses assertions.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('wythoff11_certificates'))
    args = parser.parse_args()
    verify(args.output)
