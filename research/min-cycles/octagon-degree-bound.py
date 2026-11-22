"""Check the alpha <= n bound for octagons with at least three degree-two vertices."""
from fractions import Fraction
from itertools import combinations, product
from math import lcm

import numpy as np
from scipy.optimize import linprog

from certificates import distance_labels, impact, moves_for, representative, solve

SIZE = 8
VERTICES = range(SIZE)


def cycle_distance(i, j):
    separation = abs(i - j)
    return min(separation, SIZE - separation)


def fits_degree_two(labels, vertices):
    return all(
        labels[i] == 1 + min(labels[(i - 1) % SIZE], labels[(i + 1) % SIZE])
        for i in vertices
    )


def has_exact_unit_bound(orientation, labels):
    moves = list(moves_for(orientation))
    savings = [move.saving for move in moves]
    impacts = [[impact(move, levels) for move in moves] for levels in labels]
    result = linprog(
        np.ones(len(moves)),
        A_eq=[savings],
        b_eq=[1],
        A_ub=impacts,
        b_ub=np.ones(len(impacts)),
        bounds=(0, None),
        method="highs",
    )
    if not result.success:
        return False
    rationals = [Fraction(float(weight)).limit_denominator(100_000) for weight in result.x]
    denominator = lcm(*(weight.denominator for weight in rationals))
    weights = [int(weight * denominator) for weight in rationals]
    total_saving = sum(weight * saving for weight, saving in zip(weights, savings))
    return min(weights) >= 0 and total_saving > 0 and all(
        sum(weight * change for weight, change in zip(weights, row)) <= total_saving
        for row in impacts
    )


def main():
    exterior = list(distance_labels(SIZE))
    internal = [tuple(cycle_distance(i, j) for i in VERTICES) for j in VERTICES]
    orientations = sorted({representative(bits) for bits in product((0, 1), repeat=SIZE)})
    restricted_cases = 0
    for orientation in orientations:
        bound, _ = solve(orientation, internal + exterior)
        if bound <= 1:
            continue
        for vertices in combinations(VERTICES, 3):
            labels = internal + [levels for levels in exterior if fits_degree_two(levels, vertices)]
            if not has_exact_unit_bound(orientation, labels):
                raise ArithmeticError(f"Uncovered case {orientation}, {vertices}")
            restricted_cases += 1
        print(f"{orientation}: all degree-two triples checked", flush=True)
    print(f"Checked {len(orientations)} orientations and {restricted_cases} restricted cases.")


if __name__ == "__main__":
    main()
