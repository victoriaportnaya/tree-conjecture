"""Enumerate the K4 subdivisions left by the structural inequalities."""
from itertools import combinations, permutations, product

EDGES = tuple(combinations(range(4), 2))
EDGE_INDEX = {edge: i for i, edge in enumerate(EDGES)}
CYCLES = tuple(
    tuple(EDGE_INDEX[tuple(sorted(edge))] for edge in zip(cycle, cycle[1:] + cycle[:1]))
    for cycle in (*combinations(range(4), 3), (0, 1, 2, 3), (0, 1, 3, 2), (0, 2, 1, 3))
)


def edge_permutation(vertices):
    return tuple(EDGE_INDEX[tuple(sorted((vertices[u], vertices[v])))] for u, v in EDGES)


PERMUTATIONS = tuple(permutations(range(4)))
SYMMETRIES = tuple(map(edge_permutation, PERMUTATIONS))
SPLIT_SYMMETRIES = tuple(edge_permutation(p) for p in PERMUTATIONS if set(p[:2]) == {0, 1})


def canonical(lengths, symmetries=SYMMETRIES):
    return min(tuple(lengths[i] for i in perm) for perm in symmetries)


def shortest_cycles(lengths):
    totals = tuple(sum(lengths[i] for i in cycle) for cycle in CYCLES)
    return totals, tuple(
        min(total for cycle, total in zip(CYCLES, totals) if i in cycle)
        for i in range(len(EDGES))
    )


def path_length_too_large(length, cycle):
    return length >= 5 and 3 * (1 << (length - 4)) >= 2 * (cycle - 3)


def compatible_paths(paths, depth, cycle_lengths):
    claimed_endpoints = set()
    for (start, end, length), cycle in zip(paths, cycle_lengths):
        if depth[start] > depth[end]:
            start, end = end, start
        gap = depth[end] - depth[start]
        if length >= 5 and (gap < length - 3 or path_length_too_large(length, cycle)):
            return False
        if length >= 3 and (length >= 5 or length <= gap + 2):
            if end in claimed_endpoints:
                return False
            claimed_endpoints.add(end)
    return True


def weighted_depths(paths, root, count):
    depths = [float("inf")] * count
    depths[root] = 0
    for _ in range(count - 1):
        for u, v, length in paths:
            du, dv = depths[u], depths[v]
            depths[u] = min(du, dv + length)
            depths[v] = min(dv, du + length)
    return depths


def matches_root_case(lengths, root, split=None):
    cycles, at_edge = shortest_cycles(lengths)
    if min(cycles) < 9:
        return False
    paths = tuple((*edge, length) for edge, length in zip(EDGES, lengths))
    count = 4
    if split is not None:
        paths = paths[1:] + ((0, 4, split[0]), (1, 4, split[1]))
        at_edge = at_edge[1:] + (at_edge[0], at_edge[0])
        count = 5
    return compatible_paths(paths, weighted_depths(paths, root, count), at_edge)


def candidate_lengths():
    # If the maximum-weight vertex is a branch vertex, ordinary paths have
    # length at most seven. With an internal maximum, the five ordinary
    # paths have the same bound and the two split arms have length at most eight.
    ordinary_lengths = range(1, 8)
    cases = set()
    for lengths in product(ordinary_lengths, repeat=6):
        if lengths != canonical(lengths):
            continue
        if any(matches_root_case(lengths, root) for root in range(4)):
            cases.add(lengths)
    for ordinary in product(ordinary_lengths, repeat=5):
        template = (0, *ordinary)
        if template != canonical(template, SPLIT_SYMMETRIES):
            continue
        for s, t in product(range(1, 9), repeat=2):
            lengths = (s + t, *ordinary)
            if matches_root_case(lengths, 4, (s, t)):
                cases.add(canonical(lengths))
    return sorted(cases)
