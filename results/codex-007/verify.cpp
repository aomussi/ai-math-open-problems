#include "strategy_masks.hpp"

#include <array>
#include <cstdlib>
#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using State = unsigned;
using States = std::unordered_set<State>;
constexpr unsigned history_mask = (1u << 25) - 1;
constexpr int unvisited = 99;
constexpr std::array<int, 3> step{3, 5, 0};

int digit(State h, int distance) { return (h >> (5 * (distance - 1))) & 31; }
int lap(int symbol) { return symbol ? (symbol - 1) / 3 : unvisited; }
int move(int symbol) { return symbol ? step[(symbol - 1) % 3] : 0; }
State pack(State h, int pending, int phase) { return (h << 5) | (pending << 3) | phase; }

bool admissible(State h) {
    std::array<int, 5> crossings{};
    int outgoing = 0, ending = -1;
    int target_bits = 0;
    for (int d = 5; d >= 1; --d) {
        int a = digit(h, d);
        if (!a) continue;
        int l = lap(a), m = move(a);
        if (l >= 5) return false;
        for (int e = d - 1; e >= 1; --e) {
            if (lap(digit(h, e)) == l && (d - e != 3 || m != 3)) return false;
        }
        if (!m) {
            if (ending != -1) return false;
            ending = l;
        } else if (d > m) {
            if (lap(digit(h, d - m)) != l) return false;
        } else {
            int bit = 1 << (m - d);
            if (target_bits & bit) return false;
            target_bits |= bit;
            ++outgoing;
            ++crossings[l];
        }
    }
    for (int j = 0; j < 5; ++j) {
        if (crossings[j] != (j < outgoing)) return false;
    }
    return ending == -1 || ending == outgoing;
}

bool prefer_five(int n, int v, unsigned flags) {
    int phase = v & 7;
    switch (n & 7) {
    case 1:
        if (v < 16) return (left_mask[v] >> flags) & 1;
        if (n - v <= 16) return (right_mask[n - v - 1] >> flags) & 1;
        return (interior_mask[phase] >> flags) & 1;
    case 3:
        return v >= 2 && n - v > 2 && phase <= 2;
    case 5:
        return v >= 2 && n - v > 2 &&
               (phase == 3 || phase == 4 || (phase == 5 && (flags & 1)));
    case 7: {
        if (v < 4) return (v == 1 && (flags == 13 || flags == 63)) ||
                          (v == 2 && flags == 38);
        if (n - v <= 4) return n - v == 4 && flags == 2;
        constexpr std::array<std::array<int, 5>, 8> choices{{
            {{39,-1,-1,-1,-1}}, {{55,-1,-1,-1,-1}}, {{5,25,37,-1,-1}}, {{1,2,-1,-1,-1}},
            {{9,10,25,26,37}}, {{1,2,47,63,-1}}, {{9,10,-1,-1,-1}}, {{55,61,62,63,-1}}
        }};
        for (int mask : choices[phase]) if (mask == int(flags)) return true;
        return false;
    }
    default: std::abort();
    }
}

struct Automaton {
    int n, boundary, center;
    std::unordered_map<State, std::vector<State>> interior_cache;

    std::vector<State> next(State state, int v, bool interior = false) const {
        const int order = n + (interior ? 16 : 0);
        State h = state >> 5;
        int f = (state >> 3) & 3;
        if ((state & 7) != unsigned(v & 7)) std::abort();
        auto estimate = [&](int off) {
            if (v + off == 0) return 0;
            if (v + off == order) return -1;
            int count = 0, value = unvisited;
            for (int m : {3, 5}) {
                int from = m - off;
                if (from < 1 || from > 5) continue;
                int a = digit(h, from);
                if (move(a) == m) {
                    ++count;
                    value = lap(a);
                }
            }
            return count > 1 ? unvisited + 1 : value;
        };
        int ell = estimate(0);
        if (ell > unvisited || (ell >= 5 && ell != unvisited)) return {};
        auto make = [&](int symbol, int requirement, std::vector<State>& out) {
            State nh = ((h << 5) | unsigned(symbol)) & history_mask;
            if (v >= 4 && !admissible(nh)) return;
            out.push_back(pack(nh, (f >> 1) | (requirement << 1), (v + 1) & 7));
        };
        std::vector<State> out;
        if (ell == unvisited) {
            if ((f & 1) == 0) make(0, 0, out);
            return out;
        }
        int plus1 = estimate(1), plus2 = estimate(2);
        if (plus1 > unvisited || plus2 > unvisited) return {};
        auto earlier = [&](int other, int offset) { return other < ell || (offset < 0 && other == ell); };
        bool second = (v + ell) & 1;
        if (!second) {
            make(1 + 3 * ell, 0, out);
            if (!(f & 1)) make(2 + 3 * ell, 0, out);
            return out;
        }
        std::array<int, 6> offsets{-3,-5,1,-1,2,-2};
        unsigned flags = 0;
        for (unsigned i = 0; i < offsets.size(); ++i) {
            int d = offsets[i];
            int other = d < 0 ? lap(digit(h, -d)) : (d == 1 ? plus1 : plus2);
            if (earlier(other, d)) flags |= 1u << i;
        }
        bool five = prefer_five(order, v, flags);
        bool three_blocked = v + 3 == order ||
            (move(digit(h, 2)) == 5 && earlier(lap(digit(h, 2)), 3));
        bool five_at_zero = v + 5 == order;
        bool five_possible_block = five_at_zero || earlier(plus2, 5);
        // A requirement schedules the predecessor of a previously visited +5
        // target to emit its length-three edge when that predecessor is read.
        // At +2 equal to vertex 0, the edge is enforced after wraparound.
        for (int direction = 0; direction < 3; ++direction) {
            if ((f & 1) && direction != 0) continue;
            if (direction == 0 && v + 3 == order) continue;
            if (direction == 1 && v + 5 == order) continue;
            bool needs_three = direction == 2 || (direction == 1 && !five);
            bool needs_five = direction == 2 || (direction == 0 && five);
            if (needs_three && !three_blocked) continue;
            if (needs_five && !five_possible_block) continue;
            make(1 + 3 * ell + direction, needs_five && !five_at_zero, out);
        }
        return out;
    }

    States advance(const States& current, int v) const {
        States out;
        for (State s : current) for (State t : next(s, v)) out.insert(t);
        return out;
    }

    const std::vector<State>& middle(State s) {
        auto [where, inserted] = interior_cache.try_emplace(s);
        if (inserted) where->second = next(s, boundary + ((int(s & 7) - boundary) & 7), true);
        return where->second;
    }

    void verify(const std::vector<State>& histories) {
        size_t signatures = 0, active = 0, explored = 0;
        for (State h : histories) {
            if (move(digit(h, 5)) == 5 || move(digit(h, 3)) == 3) continue;
            State bumped = 0;
            for (int d = 1; d <= 5; ++d) {
                int a = digit(h, d);
                bumped |= State(a ? a + 3 : 0) << (5 * (d-1));
            }
            for (int f = 0; f < 4; ++f) {
                ++signatures;
                States current{pack(bumped, f, 0)};
                for (int v = 0; v < boundary + center && !current.empty(); ++v) {
                    current = advance(current, v);
                }
                if (current.empty()) continue;
                ++active;
                std::vector<State> frontier(current.begin(), current.end());
                for (size_t i = 0; i < frontier.size(); ++i) {
                    for (State t : middle(frontier[i])) {
                        if (current.insert(t).second) frontier.push_back(t);
                    }
                }
                explored += current.size();
                States tail;
                for (State t : current) if ((t & 7) == unsigned((n - boundary) & 7)) tail.insert(t);
                for (int v = n - boundary; v < n && !tail.empty(); ++v) {
                    tail = advance(tail, v);
                }
                if (tail.count(pack(h, f, n & 7))) {
                    std::cerr << "Accepting state for " << n << " + 8k, history " << h
                              << " pending " << f << '\n';
                    std::exit(1);
                }
            }
        }
        std::cout << n << " + 8k: " << signatures << " signatures, "
                  << active << " active, " << explored << " reachable states, no acceptance\n";
    }
};

int main() {
    std::vector<State> histories;
    for (State raw = 0; raw < (1u << 20); ++raw) {
        State h = 0;
        for (int i = 0; i < 5; ++i) h |= ((raw >> (4 * i)) & 15) << (5 * i);
        if (admissible(h)) histories.push_back(h);
    }
    std::cout << histories.size() << " window histories\n";
    for (auto row : {std::array<int,3>{41,16,9}, {19,5,9}, {13,5,3}, {23,5,13}}) {
        Automaton{row[0],row[1],row[2],{}}.verify(histories);
    }
}
