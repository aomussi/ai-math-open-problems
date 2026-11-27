"""Finite cover of all nonnegative counter pairs and their legal move offsets.

../README.md proves that representative(k,m) preserves the full signature.
The optional verify_cover_smt.py checks coverage independently with Z3.
The main certificate uses only Python's standard library.
"""
from outcome import reduce_counters

OFFSETS = ((0, 0), (-1, 0), (1, 0), (0, -1), (1, -1))


def signature(k, m):
    result = []
    for dk, dm in OFFSETS:
        if k + dk < 0 or m + dm < 0:
            result.append(-1)
        else:
            kk, mm = reduce_counters(k + dk, m + dm)
            result.append(8 * mm + kk)
    return tuple(result)


def representative(k, m):
    """Return a pair in [0,13]^2 with exactly the same move signature.

    This explicit map is used in the written all-integer coverage proof.
    No bound on the input k or m is assumed.
    """
    assert k >= 0 and m >= 0
    if m <= 7:
        return (k if k <= 10 else 10 + k % 2, m)
    if k <= 1:
        return (k, 8 + m % 2)
    d = k - m
    if d <= -7:
        mm = 10 + m % 2
        dd = -8 + d % 2
    elif d >= 3:
        mm = 8 + m % 2
        dd = 4 - d % 2
    else:
        mm = 8 + m % 2
        dd = d
    return (mm + dd, mm)


def make_cover():
    points = {}
    for m in range(14):
        for k in range(14):
            points.setdefault(signature(k, m), (k, m))
    assert len(points) == 69
    return {
        "offsets": OFFSETS,
        "signatures": [
            {"signature": list(s), "point": list(p)}
            for s, p in points.items()
        ],
    }


if __name__ == "__main__":
    print("Counter signatures:", len(make_cover()["signatures"]))
