"""Generate the Lean certificates for a cycle with portals at 0 and 4.

Run from the project root with NumPy and SciPy installed. The solver proposes
multipliers. The checks below use Python integers, and Lean independently
checks every orientation from the emitted data.
"""
from argparse import ArgumentParser
from collections import deque
from fractions import Fraction
from itertools import product
from math import gcd, lcm
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

SIZE = 8
PORTALS = (0, 4)
EDGES = tuple((u, (u + 1) % SIZE) for u in range(SIZE))


def strategies(bits):
    purchases = [set() for _ in range(SIZE)]
    for bit, (u, v) in zip(bits, EDGES):
        buyer, target = (u, v) if bit else (v, u)
        purchases[buyer].add(target)
    return purchases


def distances(purchases, source):
    neighbors = [set() for _ in range(SIZE)]
    for u, targets in enumerate(purchases):
        for v in targets:
            neighbors[u].add(v)
            neighbors[v].add(u)
    labels = {source: 0}
    queue = deque([source])
    while queue:
        u = queue.popleft()
        for v in neighbors[u]:
            if v not in labels:
                labels[v] = labels[u] + 1
                queue.append(v)
    if len(labels) == SIZE:
        return tuple(labels[v] for v in range(SIZE))


def columns(labels):
    a, b = PORTALS
    exterior = tuple(
        min(labels[a] + max(0, offset), labels[b] + max(0, -offset))
        for offset in range(-7, 8)
    )
    return labels + exterior


def deviation_rows(bits):
    purchases = strategies(bits)
    for buyer, old in enumerate(purchases):
        before = columns(distances(purchases, buyer))
        choices = [None] + [
            v for v in range(SIZE) if v != buyer and buyer not in purchases[v]
        ]
        for target in choices:
            new = set() if target is None else {target}
            if new == old:
                continue
            changed = purchases.copy()
            changed[buyer] = new
            labels = distances(changed, buyer)
            if labels is None:
                continue
            difference = tuple(after - prev for after, prev in zip(columns(labels), before))
            yield (buyer, target), (len(new) - len(old), *difference), labels


def orientation_key(bits):
    return sum(bit << i for i, bit in enumerate(bits))


def check_combination(rows, moves):
    combined = [0] * 24
    for buyer, target, multiplier in moves:
        if multiplier <= 0:
            raise ValueError("Nonpositive deviation multiplier")
        row, _ = rows[buyer, target]
        for column, value in enumerate(row):
            combined[column] += multiplier * value
    saved = -combined[0]
    if saved <= 0 or any(value > saved for value in combined[1:]):
        raise ValueError(f"Invalid certificate {combined}")
    return saved


def propose(rows):
    matrix = np.array([row for row, _ in rows.values()])
    result = linprog(
        np.ones(len(rows)),
        A_eq=[matrix[:, 0]],
        b_eq=[-1],
        A_ub=matrix[:, 1:].T,
        b_ub=np.ones(23),
        bounds=(0, None),
        method="highs",
    )
    if not result.success:
        raise ValueError(result.message)
    rationals = [Fraction(float(value)).limit_denominator(1000) for value in result.x]
    denominator = lcm(*(value.denominator for value in rationals))
    moves = [
        (*move, int(value * denominator))
        for move, value in zip(rows, rationals)
        if value
    ]
    saved = check_combination(rows, moves)
    divisor = gcd(saved, *(weight for _, _, weight in moves))
    return [(buyer, target, weight // divisor) for buyer, target, weight in moves]


def relabel(bits, image, reflection):
    changed = [0] * SIZE
    for i, bit in enumerate(bits):
        index = image((i + 1) % SIZE) if reflection else image(i)
        changed[index] = 1 - bit if reflection else bit
    return changed


def build_certificates():
    certificates = {}
    for bits in product(range(2), repeat=SIZE):
        if orientation_key(bits) in certificates:
            continue
        rows = {move: (row, labels) for move, row, labels in deviation_rows(bits)}
        moves = propose(rows)
        for sign, offset in product((1, -1), PORTALS):
            image = tuple((sign * v + offset) % SIZE for v in range(SIZE)).__getitem__
            reflected = relabel(bits, image, sign == -1)
            key = orientation_key(reflected)
            if key in certificates:
                continue
            mapped = [
                (image(buyer), None if target is None else image(target), weight)
                for buyer, target, weight in moves
            ]
            rows = {move: (row, labels) for move, row, labels in deviation_rows(reflected)}
            check_combination(rows, mapped)
            certificates[key] = [(*move, rows[move[:2]][1]) for move in mapped]
    if len(certificates) != 256:
        raise ValueError("Missing cycle orientations")
    return certificates


def format_move(move):
    buyer, target, weight, labels = move
    option = "none" if target is None else f"some {target}"
    return f'⟨{buyer}, {option}, {weight}, ![{", ".join(map(str, labels))}]⟩'


def write_lean(path, certificates):
    lines = [
        "import TreeConjecture.TwoPortalCertificate",
        "",
        "namespace TreeConjecture.TwoPortalCertificate",
        "",
        "-- Generated from integer-verified combinations of deviation rows.",
    ]
    for group in range(16):
        lines.append(f"def moves{group} : Array (List Move) := #[")
        for index in range(16):
            moves = certificates[16 * group + index]
            lines.append("  [" + ", ".join(map(format_move, moves)) + (']' if index == 15 else '],'))
        lines.extend(("]", ""))
    lines.append("end TreeConjecture.TwoPortalCertificate")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    certificates = build_certificates()
    write_lean(args.output, certificates)
    print(f"Checked {len(certificates)} orientations and {sum(map(len, certificates.values()))} moves.")


if __name__ == "__main__":
    main()
