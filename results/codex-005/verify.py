from itertools import combinations, combinations_with_replacement
from math import comb


def masks(size, count):
    return [sum(1 << point for point in block)
            for block in combinations(range(size), count)]


def compatible_four_blocks(size, fixed):
    return [block for block in masks(size, 4)
            if all((block & large).bit_count() <= 2 for large in fixed)]


def graph(blocks, compatible):
    adjacent = [0] * len(blocks)
    for i, j in combinations(range(len(blocks)), 2):
        if compatible(blocks[i] & blocks[j]):
            adjacent[i] |= 1 << j
    return adjacent


def maximum_clique(adjacent):
    best = 0

    def extend(remaining, depth):
        nonlocal best
        best = max(best, depth)
        while depth + remaining.bit_count() > best:
            bit = remaining & -remaining
            remaining ^= bit
            vertex = bit.bit_length() - 1
            extend(remaining & adjacent[vertex], depth + 1)

    extend((1 << len(adjacent)) - 1, 0)
    return best


def count_cliques(adjacent, largest):
    counts = [0] * (largest + 1)

    def extend(remaining, depth):
        counts[depth] += 1
        if depth == largest:
            return
        while remaining:
            bit = remaining & -remaining
            remaining ^= bit
            extend(remaining & adjacent[bit.bit_length() - 1], depth + 1)

    extend((1 << len(adjacent)) - 1, 0)
    return counts


def four_block_bound(size, fixed):
    blocks = compatible_four_blocks(size, fixed)
    return maximum_clique(graph(blocks, lambda overlap: overlap.bit_count() <= 2))


def verify_nine_points():
    cases = [[31], [31, 481], [31, 227], [31, 227, 364]]
    # Pair intersections in the last case have size two and its triple
    # intersection is empty. The singleton-only points fill out each block.
    assert all(all(block.bit_count() == 5 for block in case) for case in cases)
    assert (cases[1][0] & cases[1][1]).bit_count() == 1
    assert (cases[2][0] & cases[2][1]).bit_count() == 2
    assert all((a & b).bit_count() == 2 for a, b in combinations(cases[3], 2))
    assert cases[3][0] & cases[3][1] & cases[3][2] == 0
    result = [four_block_bound(9, case) for case in cases]
    assert result == [13, 12, 10, 6], result
    print("Nine points:", result, flush=True)


def patterns_five_blocks():
    pairs, triples = masks(5, 2), masks(5, 3)
    for large in combinations_with_replacement(triples, 5):
        small = []
        for pair in pairs:
            missing = 2 - sum(point & pair == pair for point in large)
            if missing < 0:
                break
            small.extend([pair] * missing)
        else:
            candidate = (*large, *small)
            if len(candidate) == 10 and all(
                    sum(bool(point & (1 << j)) for point in candidate) == 5
                    for j in range(5)):
                yield candidate


def patterns_six_blocks():
    triples = masks(6, 3)
    pairs = masks(6, 2)
    uses = [tuple(i for i, pair in enumerate(pairs) if triple & pair == pair)
            for triple in triples]
    covered = [0] * len(pairs)
    chosen = []

    def extend(first):
        if len(chosen) == 10:
            assert covered == [2] * 15
            yield tuple(chosen)
            return
        for index in range(first, len(triples)):
            pair_indices = uses[index]
            if any(covered[i] == 2 for i in pair_indices):
                continue
            for i in pair_indices:
                covered[i] += 1
            chosen.append(triples[index])
            yield from extend(index)
            chosen.pop()
            for i in pair_indices:
                covered[i] -= 1

    yield from extend(0)


def verify_ten_points():
    for n, generator, expected in [(5, patterns_five_blocks, 7), (6, patterns_six_blocks, 5)]:
        result = []
        for membership in generator():
            block = [sum(1 << i for i, point in enumerate(membership) if point & (1 << j))
                     for j in range(n)]
            assert all(b.bit_count() == 5 for b in block)
            assert all((a & b).bit_count() == 2 for a, b in combinations(block, 2))
            result.append(four_block_bound(10, block))
        assert len(result) == 12 and max(result) == expected, (n, result)
        print("Ten points:", n, "five-element blocks,", len(result),
              "membership multisets, maximum", max(result), flush=True)


def verify_prefixes():
    common = [11, 19, 13, 21, 14, 22, 26, 28, 3, 5, 9, 17, 6, 24]
    for extra, expected in [
        ([6, 24], [1, 86, 1621, 7088, 8448, 3136, 672, 0]),
        ([10, 20], [1, 60, 704, 1664, 804, 76, 6, 0]),
    ]:
        columns = common + extra
        rows = [sum(1 << j for j, col in enumerate(columns) if col & (1 << i))
                for i in range(5)]
        assert all(row.bit_count() == 8 for row in rows)
        row_pairs = [a & b for a, b in combinations(rows, 2)]
        candidates = [
            row for row in masks(16, 8)
            if all((row & a).bit_count() == 4 for a in rows)
            and all((row & a).bit_count() <= 2 for a in row_pairs)
        ]
        adj = graph(candidates, lambda overlap: overlap.bit_count() <= 4 and
                    all((overlap & row).bit_count() <= 2 for row in rows))
        counts = count_cliques(adj, 7)
        assert counts == expected, counts
        print("Final prefix clique counts:", counts, flush=True)


def verify_lower_bound():
    rows = []
    for a in range(8):
        for b in range(2):
            indices = [2 * x + (b ^ ((a & x).bit_count() % 2)) for x in range(8)]
            if a in {0, 1}:
                indices.append(16)
            rows.append(sum(1 << index for index in indices))
    assert sum(r.bit_count() for r in rows) == 132
    tallies = [0, 0, 0]
    for a, b, c in combinations(rows, 3):
        tallies[(a & b & c).bit_count()] += 1
    assert tallies == [108, 4, 448] and sum(tallies) == comb(16, 3)
    print("132-entry witness, triple intersections:", tallies, flush=True)


if __name__ == "__main__":
    verify_lower_bound()
    verify_nine_points()
    verify_ten_points()
    verify_prefixes()
