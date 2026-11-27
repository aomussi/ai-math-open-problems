"""Exact transition antichains for the proposed B664 + H30 + H34 classifier.

No outcome equivalence or canonical simplification is assumed.  The supplied
background actions are simply a proposed homomorphism from heap multisets.
Original octal .07 moves are reconstructed and checked against the export.
Every nonempty background position has a transition set containing one of
the retained minimal sets at its label.  Empty background is kept separately.
"""
import argparse
from collections import deque
import json
import time


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def build(path="background.json", output="background_transitions.json"):
    started = time.monotonic()
    model = json.load(open(path))
    n = model["states"]
    actions = model["actions"]
    reps = model["representatives"]
    physical = [h for h in range(2, 33) if h != 30]

    # Transitive commuting actions define a commutative monoid.  Do not trust
    # an externally supplied multiplication table or any canonical identities.
    def word(word, q=0):
        for h in word:
            q = actions[h][q]
        return q

    assert all(word(w) == q for q, w in enumerate(reps))
    assert actions[0] == actions[1] == list(range(n))
    for h in physical:
        assert len(actions[h]) == n
        assert all(0 <= t < n for t in actions[h])
        for j in physical:
            assert all(actions[h][actions[j][q]] == actions[j][actions[h][q]]
                       for q in range(n)), (h, j)
    multiplication = [[word(reps[r], q) for r in range(n)] for q in range(n)]
    assert all(multiplication[q][r] == multiplication[r][q]
               for q in range(n) for r in range(n))

    options = {}
    for h in physical + [30, 34]:
        images = set()
        for a in range((h - 2) // 2 + 1):
            b = h - 2 - a
            delta = (a == 30) + (b == 30)
            q = word([t for t in (a, b) if t != 30])
            images.add((delta, q))
        assert images == set(map(tuple, model["options"][str(h)])), h
        options[h] = sorted(images)

    # Bit delta*n+q represents an option with background label q which
    # introduces delta copies of H30.  Only H32 can introduce one H30.
    def mask_of(pairs):
        mask = 0
        for delta, q in pairs:
            mask |= 1 << (delta * n + q)
        return mask

    translated_options = {
        h: [mask_of((delta, multiplication[r][q]) for delta, q in options[h])
            for r in range(n)]
        for h in physical
    }
    edges = [0] * n
    edge_witnesses = [{} for _ in range(n)]
    for h in physical:
        for r in range(n):
            q = actions[h][r]
            additions = translated_options[h][r]
            for t in bits(additions & ~edges[q]):
                edge_witnesses[q][t] = [h] + reps[r]
            edges[q] |= additions

    # Keep inclusion-minimal *nonempty-background* transition sets.  A
    # background labelled 0 need not be terminal (for example H5), hence
    # seeding the empty position here would invalidate the terminal exception.
    antichains = [dict() for _ in range(n)]
    queue = deque()
    inserted = 0

    def insert(q, mask, witness):
        nonlocal inserted
        assert mask
        current = antichains[q]
        if any(old & mask == old for old in current):
            return
        remove = [old for old in current if old & mask == mask]
        for old in remove:
            del current[old]
        current[mask] = witness
        queue.append((q, mask))
        inserted += 1

    for h in physical:
        insert(actions[h][0], translated_options[h][0], [h])
    processed = 0
    while queue:
        q, mask = queue.popleft()
        if mask not in antichains[q]:
            continue
        witness = antichains[q][mask]
        processed += 1
        if processed % 1000 == 0:
            print("progress", processed, "retained", sum(map(len, antichains)),
                  "queued", len(queue), "seconds", round(time.monotonic() - started, 2),
                  flush=True)
        entries = list(bits(mask))
        for h in physical:
            action = actions[h]
            transformed = 0
            for t in entries:
                delta, state = divmod(t, n)
                transformed |= 1 << (delta * n + action[state])
            transformed |= translated_options[h][q]
            insert(action[q], transformed, witness + [h])

    # Independent end checks: every retained pair is realized by its witness;
    # every physical single-heap seed is dominated; and the antichains are
    # closed under every generator in the required domination direction.
    for q, ac in enumerate(antichains):
        for mask, witness in ac.items():
            assert word(witness) == q
            actual = 0
            for j, h in enumerate(witness):
                rest = word(witness[:j] + witness[j + 1:])
                for delta, state in options[h]:
                    actual |= 1 << (delta * n + multiplication[rest][state])
            assert actual == mask, (q, witness)
    for h in physical:
        seed = translated_options[h][0]
        assert any(old & seed == old for old in antichains[actions[h][0]])
    for q, ac in enumerate(antichains):
        for mask in ac:
            entries = list(bits(mask))
            for h in physical:
                transformed = translated_options[h][q]
                for t in entries:
                    delta, state = divmod(t, n)
                    transformed |= 1 << (delta * n + actions[h][state])
                assert any(old & transformed == old
                           for old in antichains[actions[h][q]])

    result = {
        "background_model": path,
        "states": n,
        "physical_background_heaps": physical,
        "pair_encoding": "delta_H30 * states + background_state",
        "options": {str(h): options[h] for h in options},
        "multiplication": multiplication,
        "edges": [list(bits(e)) for e in edges],
        "edge_witnesses": edge_witnesses,
        "nonempty_antichains": [
            [{"options": list(bits(mask)), "witness": witness}
             for mask, witness in sorted(ac.items())]
            for ac in antichains
        ],
        "processed": processed,
        "inserted": inserted,
        "retained": sum(map(len, antichains)),
    }
    with open(output, "w") as f:
        json.dump(result, f, separators=(",", ":"))
    print(json.dumps({k: result[k] for k in ("states", "processed", "inserted", "retained")}),
          "seconds", round(time.monotonic() - started, 3), flush=True)
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", default="background.json")
    parser.add_argument("--output", default="background_transitions.json")
    args = parser.parse_args()
    build(args.model, args.output)
