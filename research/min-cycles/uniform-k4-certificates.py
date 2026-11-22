"""Check exact deviation certificates for uniform K4 subdivisions."""
from collections import Counter
from itertools import combinations, permutations, product

from deviation_certificate_search import bought_neighbors, exact_cut, row_cache

EDGES = tuple(combinations(range(4), 2))


def subdivision(length):
    size = 4 + len(EDGES) * (length - 1)
    adjacency = [set() for _ in range(size)]
    paths = []
    for index, (a, b) in enumerate(EDGES):
        first = 4 + index * (length - 1)
        path = (a, *range(first, first + length - 1), b)
        paths.append(path)
        for u, v in zip(path, path[1:]):
            adjacency[u].add(v)
            adjacency[v].add(u)
    return paths, adjacency


def three_edge_cases():
    # A first forward buy and a last backward buy are incompatible.
    words = tuple(w for w in range(8) if not (w & 4 and not w & 1))
    assert words == (0, 1, 2, 3, 5, 7)
    images = [
        [((p[a], p[b]) if p[a] < p[b] else (p[b], p[a]), p[a] > p[b]) for a, b in EDGES]
        for p in permutations(range(4))
    ]
    seen = set()
    for profile in product(words, repeat=len(EDGES)):
        if profile in seen:
            continue
        for image in images:
            transformed = [0] * len(EDGES)
            for word, (edge, reversed_edge) in zip(profile, image):
                transformed[EDGES.index(edge)] = (
                    int(f"{word:03b}"[::-1], 2) ^ 7 if reversed_edge else word
                )
            seen.add(tuple(transformed))
        yield profile
    if len(seen) != len(words) ** len(EDGES):
        raise ArithmeticError("Incomplete ownership enumeration")


def four_edge_cases():
    # Relabel a maximum-weight branch vertex as 0. Its three paths have the
    # last three edges bought forward. The other paths have two double buyers.
    yield from product(*((7, 15) if a == 0 else (5,) for a, _ in EDGES))


def verify(length, profiles):
    paths, adjacency = subdivision(length)
    size = len(adjacency)
    rows_at = row_cache(adjacency)
    counts = Counter()
    for profile in profiles:
        purchases = bought_neighbors(profile, paths, size, length)
        rows = [row for u, owned in enumerate(purchases) for row in rows_at[u, owned]]
        try:
            counts[exact_cut(rows, size)] += 1
        except ArithmeticError as error:
            raise ArithmeticError(f"Length {length}, ownership {profile}") from error
    print(f"Path length {length}: {dict(counts)}, total {sum(counts.values())}", flush=True)


if __name__ == "__main__":
    verify(4, four_edge_cases())
    verify(3, three_edge_cases())
