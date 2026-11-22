"""Exclude every subdivision of K4 by exact Nash certificates."""
from collections import Counter
from itertools import product

import numpy as np
from scipy.optimize import linprog

from deviation_certificate_search import distances, exact_cut, row_cache
from k4_subdivision_cases import EDGES, candidate_lengths, compatible_paths, shortest_cycles


def geometry(lengths):
    n=sum(lengths)-2
    adj=[set() for _ in range(n)]
    paths=[]
    tail=4
    for (u,v),ell in zip(EDGES,lengths):
        path=(u,*range(tail,tail+ell-1),v)
        tail+=ell-1
        for a,b in zip(path,path[1:]):
            adj[a].add(b);adj[b].add(a)
        paths.append(path)
    return adj,paths

def matches_maximum(paths, depth, root, at_edge):
    pieces = []
    cycles = []
    for path, cycle in zip(paths, at_edge):
        if root in path[1:-1]:
            index = path.index(root)
            arms = (path[:index + 1], path[index:])
        else:
            arms = (path,)
        for arm in arms:
            pieces.append((arm[0], arm[-1], len(arm) - 1))
            cycles.append(cycle)
    return compatible_paths(pieces, depth, cycles)


def orientations(path, depth):
    k=len(path)-1
    forward={i for i in range(1,k) if depth[path[i+1]]==depth[path[i-1]]+2}
    backward={i-1 for i in range(1,k) if depth[path[i-1]]==depth[path[i+1]]+2}
    for bits in product((0,1),repeat=k):
        if any(not bits[i] for i in forward) or any(bits[i] for i in backward):
            continue
        if any(bits[i] and not bits[j] for i in range(k) for j in range(i+2,k)):
            continue
        yield tuple((u,v) if bit else (v,u) for bit,(u,v) in zip(bits,zip(path,path[1:])))

def verify_subdivision(lengths):
    adjacency, paths = geometry(lengths)
    size = len(adjacency)
    pool = row_cache(adjacency)
    _, at_edge = shortest_cycles(lengths)
    counts = Counter()
    objective = np.r_[np.zeros(size), -1.]
    total_weight = np.r_[np.ones(size), 0][None, :]
    baseline = {row for v in range(size) for row in pool[v, ()]}
    baseline.add((1, *[-1] * size))
    baseline.add((-1, *[2] * size))

    for root in range(size):
        depth = distances(adjacency, root)
        if not matches_maximum(paths, depth, root, at_edge):
            continue
        choices = [list(orientations(path, depth)) for path in paths]
        if not all(choices):
            continue
        choices.sort(key=lambda alternatives: (len(alternatives), -len(alternatives[0])))
        counts["roots"] += 1
        rows = baseline | {
            (0, *(int(i == root) - int(i == v) for i in range(size)))
            for v in range(size) if v != root
        }
        owned = [[] for _ in range(size)]

        def certify(level, rows):
            # The numerical relaxation chooses when to attempt an exact cut.
            # No branch is accepted from the floating-point result alone.
            ordered = sorted(rows)
            matrix = np.array(ordered, dtype=np.int64)
            result = linprog(
                objective, A_ub=-matrix[:, [*range(1, size + 1), 0]],
                b_ub=np.zeros(len(matrix)), A_eq=total_weight, b_eq=[1],
                bounds=[(0, None)] * size + [(1, 2)], method="highs",
            )
            if result.status == 2 or (result.success and result.x[-1] <= 1 + 1e-8):
                try:
                    kind = exact_cut(ordered, size)
                except ArithmeticError:
                    pass
                else:
                    counts[kind] += 1
                    return
            if level == len(choices):
                raise ArithmeticError(f"Uncovered lengths {lengths}, root {root}, ownership {owned}")
            for arrows in choices[level]:
                buyers = set()
                for u, v in arrows:
                    owned[u].append(v)
                    buyers.add(u)
                extra = (pool[u, tuple(sorted(owned[u]))] for u in buyers)
                certify(level + 1, rows.union(*extra))
                for u, _ in arrows:
                    owned[u].pop()

        certify(0, rows)
    return counts


def main():
    lengths = candidate_lengths()
    totals = Counter()
    for shape in lengths:
        totals.update(verify_subdivision(shape))
    print(f"Checked {len(lengths)} subdivisions with core order at most {max(map(sum, lengths)) - 2}.")
    print(dict(totals))


if __name__ == "__main__":
    main()
