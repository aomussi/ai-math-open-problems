from functools import lru_cache


def winning(order):
    @lru_cache(maxsize=None)
    def search(vertex, seen):
        for step in (3, 5):
            target = (vertex + step) % order
            bit = 1 << target
            if seen & bit == 0 and not search(target, seen | bit):
                return True
        return False

    return search(0, 1)


if __name__ == "__main__":
    wins = [n for n in range(1, 34) if winning(n)]
    assert wins == sorted([*range(2, 34, 2), 9, 11, 17]), wins
    print("PASS: first-player wins through order 33:", wins)
