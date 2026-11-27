"""Optional independent all-integer coverage check.

Install z3-solver, then run this file.  This check is not a finite grid test:
the solver searches over ALL nonnegative integer k,m for an uncovered
signature.  UNSAT means no such pair exists.
"""
from z3 import Int, If, Or, Solver, unsat
from counter_cover import OFFSETS, make_cover


def cell(k, m):
    s = 4 + m % 2
    x = k - m + s
    kk = If(m >= 6, If(x >= 1, x, If(k == 0, 0, 1 + (k - 1) % 2)), k)
    mm = If(m >= 6, s, m)
    kk = If(kk >= 6, 6 + kk % 2, kk)
    return If(Or(k < 0, m < 0), -1, 8 * mm + kk)


k, m = Int("k"), Int("m")
expressions = [cell(k + dk, m + dm) for dk, dm in OFFSETS]
solver = Solver()
solver.add(k >= 0, m >= 0)
for row in make_cover()["signatures"]:
    solver.add(Or(*(expression != value for expression, value
                    in zip(expressions, row["signature"]))))
result = solver.check()
print("All-integer counter coverage:", result)
if result != unsat:
    print(solver.model() if str(result) == "sat" else solver.reason_unknown())
assert result == unsat
