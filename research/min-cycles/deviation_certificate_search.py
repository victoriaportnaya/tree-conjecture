"""Generate deviations and verify exact integer combinations of their rows."""
from collections import deque
from fractions import Fraction
from itertools import combinations
from math import lcm

import numpy as np
from scipy.optimize import linprog


def distances(adjacency, source):
    result = {source: 0}
    queue = deque([source])
    while queue:
        vertex = queue.popleft()
        for neighbor in adjacency[vertex]:
            if neighbor not in result:
                result[neighbor] = result[vertex] + 1
                queue.append(neighbor)
    if len(result) == len(adjacency):
        return tuple(result[i] for i in range(len(adjacency)))


def rows_for_buyer(adjacency, buyer, owned, columns):
    before = columns(distances(adjacency, buyer))
    targets = tuple(t for t in range(len(adjacency)) if t != buyer and t not in adjacency[buyer])
    for sold_count in range(len(owned) + 1):
        for sold in combinations(owned, sold_count):
            for target in (None, *targets):
                if not sold and target is None:
                    continue
                changed = [row.copy() for row in adjacency]
                for neighbor in sold:
                    changed[buyer].remove(neighbor)
                    changed[neighbor].remove(buyer)
                if target is not None:
                    changed[buyer].add(target)
                    changed[target].add(buyer)
                after = distances(changed, buyer)
                if after is not None:
                    yield (int(target is not None) - sold_count, *(
                        new - old for new, old in zip(columns(after), before)
                    ))


def row_cache(adjacency, columns=lambda labels: labels):
    return {
        (buyer, owned): tuple(rows_for_buyer(adjacency, buyer, owned, columns))
        for buyer, incident in enumerate(adjacency)
        for count in range(len(incident) + 1)
        for owned in combinations(sorted(incident), count)
    }


def exact_combination(rows, proposed):
    coefficients = [Fraction(float(mult)).limit_denominator(100_000) for mult in proposed]
    scale = lcm(*(value.denominator for value in coefficients))
    combined = [0] * len(rows[0])
    for row, value in zip(rows, coefficients):
        weight = int(scale * value)
        if weight < 0:
            raise ArithmeticError("Negative proposed multiplier")
        if weight:
            for index, entry in enumerate(row):
                combined[index] += weight * entry
    return combined


def exact_cut(rows, size):
    matrix = np.array(rows, dtype=np.int64)
    objective = np.ones(len(rows))
    price_bound = linprog(
        objective, A_eq=[matrix[:, 0]], b_eq=[-1],
        A_ub=matrix[:, 1:].T, b_ub=np.ones(size), bounds=(0, None), method="highs",
    )
    if price_bound.success:
        price, *distance = exact_combination(rows, price_bound.x)
        if price < 0 and max(distance) <= -price:
            return "price"
    infeasible = linprog(
        objective, A_ub=matrix.T, b_ub=[0] + [-1] * size,
        bounds=(0, None), method="highs",
    )
    if infeasible.success:
        price, *distance = exact_combination(rows, infeasible.x)
        if price <= 0 and max(distance) < 0:
            return "infeasible"
    raise ArithmeticError("No exact certificate")


def bought_neighbors(words, paths, size, length):
    purchases = [[] for _ in range(size)]
    for word, path in zip(words, paths):
        for bit, (u, v) in zip(f"{word:0{length}b}", zip(path, path[1:])):
            buyer, neighbor = (u, v) if bit == "1" else (v, u)
            purchases[buyer].append(neighbor)
    return [tuple(sorted(owned)) for owned in purchases]
