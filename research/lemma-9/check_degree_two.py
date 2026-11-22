from itertools import combinations
from random import Random
from pathlib import Path
import sys

project = Path(sys.argv[1] if len(sys.argv) > 1 else ".").resolve()
sys.path.insert(0, str(project))
from ncg import distance_rows

def distances(n, adjacency, root):
    return [distance if distance is not None else -1 for distance in distance_rows(adjacency, root)]

def candidates(n, rng):
    edges = list(combinations(range(n), 2))
    if n <= 6:
        masks = range(1 << len(edges))
    else:
        masks = (rng.getrandbits(len(edges)) for _ in range(1500))
    for mask in masks:
        adjacency = [0] * n
        for index, (u, v) in enumerate(edges):
            if mask & (1 << index):
                adjacency[u] |= 1 << v
                adjacency[v] |= 1 << u
        if all(x >= 0 for x in distances(n, adjacency, 0)):
            yield adjacency

def check(adjacency):
    n = len(adjacency)
    g = [distances(n, adjacency, u) for u in range(n)]
    verified = 0
    for v, neighbors in enumerate(adjacency):
        reduced = [row & ~(1 << v) for row in adjacency]
        reduced[v] = 0
        for u in range(n):
            if not neighbors & (1 << u):
                continue
            avoiding = distances(n, reduced, u)
            kept = [x for x in range(n) if neighbors & (1 << x) and avoiding[x] >= 0]
            if len(kept) != 2:
                continue
            w = next(x for x in kept if x != u)
            arm = avoiding[w]
            if arm < 2:
                continue
            A = [d < 0 for d in avoiding]
            B = [ku == 2 + kw for ku, kw in zip(g[u], g[w])]
            assert not any(a and b for a, b in zip(A, B))
            deleted = adjacency.copy()
            deleted[u] &= ~(1 << v)
            deleted[v] &= ~(1 << u)
            swapped = deleted.copy()
            swapped[u] |= 1 << w
            swapped[w] |= 1 << u
            swap_d = distances(n, swapped, u)
            del_d = distances(n, deleted, u)
            assert all(k >= 0 for k in swap_d + del_d)
            for x in range(n):
                assert swap_d[x] - g[u][x] <= A[x] - B[x]
                assert del_d[x] - g[u][x] <= arm * A[x] + (arm - 2) * B[x]
            if sum(swap_d) >= sum(g[u]):
                assert sum(B) <= sum(A)
                assert sum(del_d) - sum(g[u]) <= 2 * (arm - 1) * sum(A)
            verified += 1
    return verified

rng = Random(224)
total = 0
for n in range(3, 11):
    graphs = count = 0
    for adjacency in candidates(n, rng):
        graphs += 1
        count += check(adjacency)
    total += count
    print(f"n={n}: {graphs} connected graphs, {count} eligible ordered triples", flush=True)
print(f"total eligible ordered triples: {total}")
