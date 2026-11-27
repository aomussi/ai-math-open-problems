#!/usr/bin/env python3
"""Exact checker for the K_(1,4) versus path Builder certificate.

Python 3 standard library only. All mathematical checks use integers.
The checker regenerates legal graph transitions; it does not trust transitions
or costs copied into the certificate. State isomorphism uses explicit tuples,
independently of the packed integer encoding used in the strategy search.
"""
import itertools
import json
from collections import deque
from pathlib import Path
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def state_from_row(row):
    degrees = tuple(row['red_degrees'])
    components = tuple(tuple(c) for c in row['components'])
    red = frozenset(tuple(e) for e in row['red_edges'])
    n = len(degrees)
    require(1 <= n <= 8, 'Invalid number of boundary vertices')
    require(1 <= len(components) <= 4, 'Invalid number of paths')
    require(all(len(c) in (1, 2) for c in components), 'Invalid path boundary')
    require(sorted(v for c in components for v in c) == list(range(n)),
            'Path boundaries do not partition the boundary vertices')
    require(all(type(d) is int and 0 <= d <= 3 for d in degrees),
            'Invalid red degree')
    comp = {v: j for j, c in enumerate(components) for v in c}
    require(len(red) == len(row['red_edges']), 'Duplicate red edge')
    for u, v in red:
        require(0 <= u < v < n, 'Invalid red edge endpoints')
        require(comp[u] != comp[v], 'Only cross-component red edges are stored')
    for v in range(n):
        require(sum(v in e for e in red) <= degrees[v], 'Red degree too small')
    return degrees, components, red


def canonical_key(state):
    """Canonical explicit-tuple encoding, by path permutations and reversals."""
    degrees, components, red = state
    comp = {v: j for j, c in enumerate(components) for v in c}
    cross = frozenset(e for e in red if comp[e[0]] != comp[e[1]])
    candidates = []
    for perm in itertools.permutations(components):
        orientations = [(c, c[::-1]) if len(c) == 2 else (c,) for c in perm]
        for oriented in itertools.product(*orientations):
            order = tuple(v for c in oriented for v in c)
            inverse = {old: new for new, old in enumerate(order)}
            dr = tuple(degrees[v] for v in order)
            lengths = tuple(len(c) for c in oriented)
            edges = tuple(sorted(tuple(sorted((inverse[u], inverse[v])))
                                 for u, v in cross))
            candidates.append((dr, lengths, edges))
    return min(candidates)


def add_isolate(state):
    degrees, components, red = state
    require(len(components) < 4, 'Cannot add a fifth path')
    n = len(degrees)
    return degrees + (0,), components + ((n,),), red


def red_edge(state, u, v):
    degrees, components, red = state
    require(degrees[u] < 3 and degrees[v] < 3, 'Red would already win')
    d = list(degrees)
    d[u] += 1
    d[v] += 1
    return tuple(d), components, red | {(min(u, v), max(u, v))}


def join_paths(state, u, v):
    """Works for a direct blue edge or a two-edge fresh-vertex connector."""
    degrees, components, red = state
    cu = next(c for c in components if u in c)
    cv = next(c for c in components if v in c)
    require(cu != cv, 'A join must use distinct paths')
    removed = set()
    new_ends = []
    for c, selected in ((cu, u), (cv, v)):
        if len(c) == 1:
            new_ends.append(selected)
        else:
            removed.add(selected)
            new_ends.append(next(w for w in c if w != selected))
    retained = [w for w in range(len(degrees)) if w not in removed]
    index = {w: j for j, w in enumerate(retained)}
    new_degrees = tuple(degrees[w] for w in retained)
    new_components = tuple(tuple(index[w] for w in c)
                           for c in components if c not in (cu, cv))
    new_components += (tuple(index[w] for w in new_ends),)
    new_red = frozenset(tuple(sorted((index[a], index[b])))
                        for a, b in red if a not in removed and b not in removed)
    return new_degrees, new_components, new_red


def regenerate(state, action):
    """Return every nonterminal Painter response as (state, cost, vertex_gain)."""
    degrees, components, red = state
    if action == ['add']:
        return [(add_isolate(state), 0, 1)]
    require(len(action) == 3, 'Invalid action')
    kind, u, v = action
    require(type(u) is int and type(v) is int and 0 <= u < v < len(degrees),
            'Invalid chosen endpoints')
    comp = {w: j for j, c in enumerate(components) for w in c}
    require(comp[u] != comp[v], 'Chosen endpoints belong to one path')
    if kind == 'bridge':
        require(degrees[u] == degrees[v] == 3, 'Bridge endpoints not saturated')
        return [(join_paths(state, u, v), 2, 1)]
    require(kind == 'edge', 'Unknown action')
    require((u, v) not in red, 'Chosen cross-edge is already exposed')
    outcomes = [(join_paths(state, u, v), 1, 0)]
    if degrees[u] < 3 and degrees[v] < 3:
        outcomes.append((red_edge(state, u, v), 1, 0))
    return outcomes


def verify(path):
    data = json.loads(Path(path).read_text(encoding='utf-8'))
    require(data['ratio'] == [9, 5], 'Unexpected coefficient')
    rows = data['states']
    require(data['initial_state'] == 0, 'Unexpected initial state')
    states = [state_from_row(row) for row in rows]
    require(states[0] == ((0,), ((0,),), frozenset()), 'Incorrect initial board')
    require(rows[0]['potential'] == 0, 'Initial potential must be zero')
    require(all(type(row['potential']) is int and row['potential'] >= 0
                for row in rows), 'Potentials must be nonnegative integers')
    keys = [canonical_key(s) for s in states]
    index = {key: i for i, key in enumerate(keys)}
    require(len(index) == len(states), 'Duplicate isomorphic states')
    queue = deque([0])
    reached = {0}
    branches = 0
    margins = []
    while queue:
        i = queue.popleft()
        row = rows[i]
        actual = []
        for successor, cost, gain in regenerate(states[i], row['action']):
            key = canonical_key(successor)
            require(key in index, f'Missing successor of state {i}')
            j = index[key]
            actual.append([j, cost, gain])
            margin = row['potential'] - rows[j]['potential'] - (5*cost - 9*gain)
            require(margin >= 0, f'Potential inequality fails at {i} -> {j}')
            margins.append(margin)
            branches += 1
            if j not in reached:
                reached.add(j)
                queue.append(j)
        require(actual == row['outcomes'], f'Recorded transitions differ at state {i}')
    require(len(reached) == len(states), 'Certificate contains unreachable rows')
    report = {
        'verified': True,
        'coefficient': '9/5',
        'reachable_states': len(states),
        'nonterminal_painter_branches': branches,
        'initial_potential': 0,
        'potential_min': min(row['potential'] for row in rows),
        'potential_max': max(row['potential'] for row in rows),
        'smallest_slack': min(margins),
        'largest_slack': max(margins),
        'inequality': '5 * cost - 9 * added_vertices <= potential_before - potential_after'
    }
    print(json.dumps(report, ensure_ascii=False, indent=2))
    return report


if __name__ == '__main__':
    default = Path(__file__).with_name('strategy.json')
    verify(sys.argv[1] if len(sys.argv) > 1 else default)
