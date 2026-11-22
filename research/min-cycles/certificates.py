"""Search weighted Nash inequalities from one isometric cycle.

SciPy proposes dual coefficients. Integer arithmetic recomputes every
certificate inequality before the coefficients can be emitted for Lean.
"""
from __future__ import annotations

import argparse
from collections import deque
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations, product
from math import lcm
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, linprog, milp


@dataclass(frozen=True)
class Move:
    buyer: int
    sold: tuple[int, ...]
    links: tuple[int, ...]
    routes: tuple[tuple[int, ...], ...]

    @property
    def saving(self) -> int:
        return len(self.sold) - len(self.links)


def cycle_edges(size: int) -> list[tuple[int, int]]:
    return [(i, (i + 1) % size) for i in range(size)]


def paths(size: int, edges: list[tuple[int, int]], start: int):
    """Return routes omitting the start, or None if an endpoint is unreachable."""
    adjacency = [[] for _ in range(size)]
    for i, j in edges:
        adjacency[i].append(j)
        adjacency[j].append(i)
    routes: list[tuple[int, ...] | None] = [None] * size
    routes[start] = ()
    frontier = deque([start])
    while frontier:
        i = frontier.popleft()
        for j in adjacency[i]:
            if routes[j] is None:
                routes[j] = (*routes[i], j)
                frontier.append(j)
    if any(route is None for route in routes):
        return None
    return tuple(routes)


def distance_labels(size: int):
    for increments in product((-1, 0, 1), repeat=size - 1):
        if abs(sum(increments)) > 1:
            continue
        levels = [0]
        for step in increments:
            levels.append(levels[-1] + step)
        minimum = min(levels)
        yield tuple(level - minimum for level in levels)


def moves_for(orientation: tuple[int, ...], *, all_links: bool = False):
    """Generate deviations whose routes keep the entire cycle vertex set connected."""
    size = len(orientation)
    cycle = cycle_edges(size)
    for buyer in range(size):
        owned = tuple(
            edge[1 - direction]
            for edge, direction in zip(cycle, orientation)
            if edge[direction] == buyer
        )
        adjacent = {j if i == buyer else i for i, j in cycle if buyer in (i, j)}
        chords = tuple(j for j in range(size) if j != buyer and j not in adjacent)
        largest = len(chords) if all_links else 1
        additions = [links for count in range(largest + 1) for links in combinations(chords, count)]
        for mask in product((False, True), repeat=len(owned)):
            sold = tuple(sorted(j for j, bit in zip(owned, mask) if bit))
            if not sold and not all_links:
                continue
            for links in additions:
                if not (sold or links):
                    continue
                remaining = [
                    (i, j)
                    for i, j in cycle
                    if (i != buyer or j not in sold) and (j != buyer or i not in sold)
                ]
                remaining.extend((buyer, link) for link in links)
                routes = paths(size, remaining, buyer)
                if routes is not None:
                    yield Move(buyer, sold, links, routes)

def impact(move: Move, levels: tuple[int, ...]) -> int:
    size = len(levels)
    before = levels[move.buyer]
    choices = [0] if all(before != levels[j] + 1 for j in move.sold) else []
    for j, route in enumerate(move.routes):
        gap = abs(j - move.buyer)
        if levels[j] < before + min(gap, size - gap):
            choices.append(len(route) + levels[j] - before)
    if not choices:
        raise ArithmeticError("No distance bound for a certified route")
    return min(choices)


def solve(orientation: tuple[int, ...], labels: list[tuple[int, ...]]):
    moves = list(moves_for(orientation))
    matrix = [[impact(move, levels) for levels in labels] for move in moves]
    constraints = np.column_stack((-np.array(matrix), [move.saving for move in moves]))
    result = linprog(
        [0] * len(labels) + [-1],
        A_ub=constraints,
        b_ub=np.zeros(len(moves)),
        A_eq=[[1] * len(labels) + [0]],
        b_eq=[1],
        bounds=(0, None),
        method="highs",
    )
    if not result.success:
        raise ArithmeticError(result.message)
    dual = [Fraction(float(-x)).limit_denominator(100_000) for x in result.ineqlin.marginals]
    denominator = lcm(*(x.denominator for x in dual))
    weights = [int(x * denominator) for x in dual]
    if any(w < 0 for w in weights):
        raise ArithmeticError("Negative certificate weight")
    savings = sum(weight * move.saving for weight, move in zip(weights, moves))
    if savings <= 0:
        raise ArithmeticError("Certificate does not save any purchases")
    bound = Fraction(max(
        sum(weight * value for weight, value in zip(weights, column))
        for column in zip(*matrix)
    ), savings)
    certificate = [(weight, move) for weight, move in zip(weights, moves) if weight]
    return bound, certificate


def representative(orientation: tuple[int, ...]) -> tuple[int, ...]:
    size = len(orientation)
    return min(
        min(
            tuple(orientation[(base + i) % size] for i in range(size)),
            tuple(1 - orientation[(base - i - 1) % size] for i in range(size)),
        )
        for base in range(size)
    )


def unit_bound_certificate(orientation: tuple[int, ...], labels: list[tuple[int, ...]]):
    """Find a small nonnegative integer certificate for alpha <= n."""
    moves = list(moves_for(orientation))
    rows = [[impact(move, levels) - move.saving for move in moves] for levels in labels]
    rows.append([-move.saving for move in moves])
    limits = [0] * len(labels) + [-1]
    count = len(moves)
    result = milp(
        np.ones(count),
        integrality=np.ones(count),
        bounds=Bounds(0, np.inf),
        constraints=LinearConstraint(np.array(rows), -np.inf, limits),
        options={"time_limit": 5},
    )
    if result.x is None:
        bound, certificate = solve(orientation, labels)
        if bound > 1:
            raise ArithmeticError("No certificate for the unit bound")
        return certificate
    weights = [round(float(value)) for value in result.x]
    if min(weights) < 0 or any(
        sum(coefficient * weight for coefficient, weight in zip(row, weights)) > limit
        for row, limit in zip(rows, limits)
    ):
        raise ArithmeticError("Integer certificate failed exact checking")
    return [(weight, move) for weight, move in zip(weights, moves) if weight]


def lean_list(items) -> str:
    return "[" + ", ".join(map(str, items)) + "]"


def emit_pentagon(cases, output: Path) -> None:
    moves = dict.fromkeys(move for _, cert in cases for _, move in cert)
    names = {move: f"move{i}" for i, move in enumerate(moves)}
    lines = [
        "import TreeConjecture.CycleCertificate",
        "import Mathlib.Data.Fin.VecNotation",
        "",
        "set_option warningAsError true",
        "",
        "namespace TreeConjecture.CycleCertificate",
        "",
        "/- Generated by research/min-cycles/certificates.py. The proof in",
        "   Pentagon.lean checks these data in Lean. -/",
        "",
    ]
    for move, name in names.items():
        target = f"some {move.links[0]}" if move.links else "none"
        routes = lean_list(map(lean_list, move.routes))
        lines.append(f"private def {name} : Move 5 :=")
        lines.append(f"  ⟨{move.buyer}, {lean_list(move.sold)}, {target}, !{routes}⟩")
    lines.extend([
        "",
        "def pentagonCertificate (o : Orientation 5) : WeightedMoves 5 :=",
        "  match o 0, o 1, o 2, o 3, o 4 with",
    ])
    for orientation, cert in cases:
        bits = ", ".join("true" if bit else "false" for bit in orientation)
        terms = lean_list(f"({weight}, {names[move]})" for weight, move in cert)
        lines.append(f"  | {bits} => {terms}")
    lines.extend(["", "end TreeConjecture.CycleCertificate", ""])
    output.write_text("\n".join(lines))


def emit_representatives(size: int, cases, output: Path) -> None:
    moves = dict.fromkeys(move for _, cert in cases for _, move in cert)
    names = {move: f"move{i}" for i, move in enumerate(moves)}
    lines = [
        "import TreeConjecture.CycleSymmetry",
        "import Mathlib.Data.Fin.VecNotation",
        "",
        "set_option warningAsError true",
        "",
        f"namespace TreeConjecture.CycleCertificate.Cycle{size}",
        "",
        "/- Generated by research/min-cycles/certificates.py. -/",
        "",
    ]
    for move, name in names.items():
        target = f"some {move.links[0]}" if move.links else "none"
        routes = lean_list(map(lean_list, move.routes))
        lines.append(f"private def {name} : Move {size} :=")
        lines.append(f"  ⟨{move.buyer}, {lean_list(move.sold)}, {target}, !{routes}⟩")
    for i, (orientation, cert) in enumerate(cases):
        bits = lean_list("true" if bit else "false" for bit in orientation)
        weighted = lean_list(f"({weight}, {names[move]})" for weight, move in cert)
        lines.extend(["", f"def cert{i} : Orientation {size} × WeightedMoves {size} :=",
                      f"  ⟨!{bits}, {weighted}⟩"])
    certs = lean_list(f"cert{i}" for i in range(len(cases)))
    lines.extend(["", f"def certificates : Representatives {size} := {certs}", "",
                  f"end TreeConjecture.CycleCertificate.Cycle{size}", ""])
    output.write_text("\n".join(lines))


def verify_octagon_witnesses():
    """Check the feasible fractional label weights against all cycle-only moves."""
    from octagon_example import FAMILIES

    labels = set(distance_labels(8))
    bounds = {}
    for bits, family in FAMILIES.items():
        weights = {levels: step for levels, _, step in family.hubs}
        if sum(weights.values()) != family.order_increment or not set(weights) <= labels:
            raise ArithmeticError("Invalid octagon label weights")
        moves = list(moves_for(tuple(map(int, bits)), all_links=True))
        for move in moves:
            total = sum(weight * impact(move, label) for label, weight in weights.items())
            if family.price_increment * move.saving > total:
                raise ArithmeticError("A cycle-only deviation violates the rational witness")
        bounds[bits] = Fraction(family.price_increment, family.order_increment)
        print(bits, "relaxation witness", bounds[bits], "with", len(moves), "checked deviations")
    return bounds


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("size", type=int, choices=range(5, 9))
    parser.add_argument("--emit-lean", type=Path)
    args = parser.parse_args()
    if args.emit_lean and args.size == 8:
        parser.error("--emit-lean supports cycle lengths five through seven")
    labels = list(distance_labels(args.size))
    cases = []
    largest = Fraction()
    octagon_bounds = {}
    for orientation in product((0, 1), repeat=args.size):
        if args.size >= 6 and orientation != representative(orientation):
            continue
        if args.size in (6, 7):
            certificate = unit_bound_certificate(orientation, labels)
            saving = sum(weight * move.saving for weight, move in certificate)
            bound = Fraction(max(
                sum(weight * impact(move, levels) for weight, move in certificate)
                for levels in labels
            ), saving)
        else:
            bound, certificate = solve(orientation, labels)
        if args.size == 8:
            octagon_bounds[''.join(map(str, orientation))] = bound
        largest = max(largest, bound)
        cases.append((orientation, certificate))
    print(args.size, "cycle vertices,", len(labels), "label types,",
          len(cases), "ownership patterns, exact certified upper bound", largest)
    if args.size == 8:
        if len(octagon_bounds) != 22:
            raise ArithmeticError("Wrong number of octagon representatives")
        for bits, bound in octagon_bounds.items():
            print(bits, bound)
        exceptions = {bits: bound for bits, bound in octagon_bounds.items() if bound > 1}
        if exceptions != verify_octagon_witnesses():
            raise ArithmeticError("The octagon bounds must match both exceptional witnesses")
    if args.emit_lean and args.size == 5:
        if largest > Fraction(6, 7):
            raise ArithmeticError("Coefficients do not prove the pentagon bound")
        emit_pentagon(cases, args.emit_lean)
    elif args.emit_lean:
        emit_representatives(args.size, cases, args.emit_lean)


if __name__ == "__main__":
    main()
