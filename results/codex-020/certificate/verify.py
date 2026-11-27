"""Universal original-move check for B664+k H30+m H34.

The separate counter-cover lemma reduces N^2 to the supplied 69 signatures.
This program verifies the outcome recursion at every such signature, using
the exact antichain certificate for *all* finite background multisets.

Run without --reuse to rebuild and verify the background certificate from
original .07 moves.  --reuse is only for development after that build passed.
"""
import argparse
import json
import time

from outcome import outcome, reduce_counters, P
from background import build
from counter_cover import make_cover
from pathlib import Path
import os
os.chdir(Path(__file__).resolve().parent)


def bitmask(values):
    result = 0
    for value in values:
        result |= 1 << value
    return result


def verify(transitions):
    started = time.monotonic()
    n = transitions["states"]
    multiplication = transitions["multiplication"]
    options = transitions["options"]
    edges = [bitmask(row) for row in transitions["edges"]]
    antichains = [[(bitmask(row["options"]), row["witness"])
                   for row in ac]
                  for ac in transitions["nonempty_antichains"]]
    signatures = make_cover()
    offsets = list(map(tuple, signatures["offsets"]))
    assert offsets == [(0, 0), (-1, 0), (1, 0), (0, -1), (1, -1)]
    checked = {"counter_signatures": 0, "P_background_edges": 0,
               "P_D_options": 0, "P_E_options": 0,
               "N_nonempty_antichains": 0, "empty_backgrounds": 0}

    for row in signatures["signatures"]:
        k, m = row["point"]
        actual_signature = []
        p_masks = []
        for dk, dm in offsets:
            if k + dk < 0 or m + dm < 0:
                actual_signature.append(-1)
                p_masks.append(0)
            else:
                kk, mm = reduce_counters(k + dk, m + dm)
                actual_signature.append(8 * mm + kk)
                p_masks.append(bitmask(b for b in range(n)
                                       if outcome(b, k + dk, m + dm)))
        assert actual_signature == row["signature"]
        checked["counter_signatures"] += 1
        p0, p_down, p_up, p_e0, p_e1 = p_masks
        p_background_targets = p0 | (p_up << n)

        for b in range(n):
            is_p = bool(p0 & (1 << b))
            d_targets = [multiplication[b][t] for delta, t in options["30"]]
            assert all(delta == 0 for delta, t in options["30"])
            e_targets = [(delta, multiplication[b][t])
                         for delta, t in options["34"]]
            d_winning = k > 0 and any(p_down & (1 << t) for t in d_targets)
            e_winning = m > 0 and any(
                (p_e0 if delta == 0 else p_e1) & (1 << t)
                for delta, t in e_targets)
            counter_winning = d_winning or e_winning

            if is_p:
                # Every possible original background move at this label is
                # included: the remainder can be any of the 664 labels.
                bad = edges[b] & p_background_targets
                if bad:
                    target = (bad & -bad).bit_length() - 1
                    witness = transitions["edge_witnesses"][b].get(str(target))
                    if witness is None:
                        witness = transitions["edge_witnesses"][b].get(target)
                    raise AssertionError(("P has P background option", b, k, m,
                                          target, witness))
                checked["P_background_edges"] += edges[b].bit_count()
                if k:
                    checked["P_D_options"] += len(d_targets)
                    assert not d_winning, ("P has P D option", b, k, m)
                if m:
                    checked["P_E_options"] += len(e_targets)
                    assert not e_winning, ("P has P E option", b, k, m)
            elif not counter_winning:
                # Any actual nonempty background transition set contains a
                # retained minimal set.  Intersecting each minimal set with
                # the P targets is therefore sufficient for every position.
                for mask, witness in antichains[b]:
                    checked["N_nonempty_antichains"] += 1
                    assert mask & p_background_targets, (
                        "N has no P option", b, k, m, witness)

            # Empty background has label 0 but no background options.  It
            # must be checked separately from nonempty positions labelled 0.
            if b == 0:
                checked["empty_backgrounds"] += 1
                if k == 0 and m == 0:
                    assert not is_p, "The terminal misere position must be N"
                elif not is_p:
                    assert counter_winning, ("Empty-background N has no P option", k, m)

    checked["background_antichains"] = transitions["retained"]
    checked["seconds"] = round(time.monotonic() - started, 3)
    print("ALL ORIGINAL MOVE CONDITIONS PASSED", json.dumps(checked), flush=True)
    with open("verification_result.json", "w") as f:
        json.dump(checked, f, indent=2)
    return checked


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--reuse", action="store_true")
    args = parser.parse_args()
    if args.reuse:
        data = json.load(open("background_transitions.json"))
    else:
        data = build()
    verify(data)
    h25 = json.load(open("background.json"))["actions"][25][0]
    for m in range(2, 6):
        assert P[h25][m] == [int(k >= m and (k-m) % 2 == 0) for k in range(8)]
    print("H25 THRESHOLD ROWS PASSED; see ../README.md for the all-integer deduction.")
