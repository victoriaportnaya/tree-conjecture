"""Command-line experiments and replayable refutation certificates."""
import argparse
from fractions import Fraction
from itertools import combinations, permutations, product
import json
from pathlib import Path

from ncg import (
    MODES, Bounds, Profile, bits, bounds_for, cycle_report, deviations,
    distance_rows, evaluate_deviation, min_cycles, target_mask,
)


def read_json(path):
    return json.loads(Path(path).read_text())


def write_json(data):
    print(json.dumps(data, indent=2))


def nonnegative(value):
    try:
        number = Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise argparse.ArgumentTypeError(f"invalid rational number: {value}") from error
    if number < 0:
        raise argparse.ArgumentTypeError("expected a nonnegative threshold")
    return number


def refutation(profile, bounds, threshold):
    return {
        "purchases": profile.as_lists(),
        "above": str(threshold),
        "witnesses": [deviation.as_dict() for deviation in bounds.witnesses(threshold)],
    }


def verify(certificate):
    profile = Profile.from_lists(certificate["purchases"])
    threshold = nonnegative(certificate["above"])
    bounds = Bounds()
    for witness in certificate["witnesses"]:
        targets = target_mask(witness["targets"], profile.n)
        calculated = evaluate_deviation(profile, witness["player"], targets)
        if calculated is None or calculated.as_dict() != witness:
            raise ValueError(f"invalid deviation witness: {witness}")
        bounds.add(calculated)
    if not bounds.excludes_above(threshold):
        raise ValueError("the stated inequalities do not refute equilibrium above the threshold")
    return {"verified": True, "above": str(threshold), "witnesses": len(certificate["witnesses"])}


def smt_number(x):
    x = Fraction(x)
    numerator = str(abs(x.numerator))
    magnitude = numerator if x.denominator == 1 else f"(/ {numerator} {x.denominator})"
    return f"(- {magnitude})" if x < 0 else magnitude


def smt_query(inequalities, threshold):
    lines = ["(set-logic QF_LRA)", "(declare-const alpha Real)",
             f"(assert (> alpha {smt_number(threshold)}))"]
    for deviation in inequalities:
        lines.append(f"; player {deviation.player} buys {list(bits(deviation.targets))}")
        lines.append(f"(assert (>= (+ (* {smt_number(deviation.a)} alpha) "
                     f"{smt_number(deviation.b)}) 0))")
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


def analyze(profile, threshold, smt_path):
    if None in distance_rows(profile.adjacency(), 0):
        if smt_path:
            raise ValueError("SMT export requires a connected initial graph")
        return {"purchases": profile.as_lists(), "connected": False,
                "equilibrium_interval": {"empty": True, "reason": "star deviation"},
                "star_deviation": {"player": 0, "targets": list(range(1, profile.n))}}
    inequalities = list(deviations(profile))
    full_bounds = Bounds()
    for inequality in inequalities:
        full_bounds.add(inequality)
    result = {
        "purchases": profile.as_lists(), "connected": True,
        "tree": sum(mask.bit_count() for mask in profile.adjacency()) == 2 * (profile.n - 1),
        "above": str(threshold),
        "equilibrium_interval": full_bounds.as_dict(),
        "single_deletion_bounds": bounds_for(profile, "delete").as_dict(),
        "single_edit_and_swap_bounds": bounds_for(profile, "swap").as_dict(),
        "finite_nondominated_deviations_checked": len(inequalities),
        "min_cycles": [cycle_report(profile, cycle, inequalities) for cycle in min_cycles(profile)],
    }
    if full_bounds.excludes_above(threshold):
        result["refutation"] = refutation(profile, full_bounds, threshold)
    if smt_path:
        Path(smt_path).write_text(smt_query(inequalities, threshold))
    return result


def graph_masks(n, edges, triangle_free, square_free=False):
    """Enumerate labelled graphs, optionally pruning short cycles as edges are added."""
    if not triangle_free and not square_free:
        yield from range(1 << len(edges))
        return

    adjacency = [0] * n

    def extend(index, mask):
        if mask.bit_count() + len(edges) - index < n:
            return
        if index == len(edges):
            yield mask
            return
        yield from extend(index + 1, mask)
        u, v = edges[index]
        if triangle_free and adjacency[u] & adjacency[v]:
            return
        if square_free and any(adjacency[w] & adjacency[v] for w in bits(adjacency[u])):
            return
        adjacency[u] |= 1 << v
        adjacency[v] |= 1 << u
        yield from extend(index + 1, mask | (1 << index))
        adjacency[u] ^= 1 << v
        adjacency[v] ^= 1 << u

    yield from extend(0, 0)


def representatives(n, triangle_free, square_free=False):
    """Connected non-tree graph representatives under all vertex permutations."""
    edges = list(combinations(range(n), 2))
    edge_bits = [[0] * n for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        edge_bits[u][v] = edge_bits[v][u] = 1 << i
    maps = [
        tuple(edge_bits[permutation[u]][permutation[v]] for u, v in edges)
        for permutation in permutations(range(n))
    ]
    seen = set()
    for mask in graph_masks(n, edges, triangle_free, square_free):
        if mask in seen or mask.bit_count() < n:
            continue
        indices = tuple(bits(mask))
        graph_edges = [edges[i] for i in indices]
        adjacency = [0] * n
        for u, v in graph_edges:
            adjacency[u] |= 1 << v
            adjacency[v] |= 1 << u
        if None in distance_rows(adjacency, 0):
            continue
        seen.update(sum(mapping[i] for i in indices) for mapping in maps)
        yield graph_edges


def orientations(n, edges):
    for owners in product((0, 1), repeat=len(edges)):
        purchases = [0] * n
        for (u, v), owner in zip(edges, owners):
            if owner:
                u, v = v, u
            purchases[u] |= 1 << v
        yield Profile(tuple(purchases))


def scan(n, threshold, keep_triangles, keep_squares=False):
    triangle_free = not keep_triangles and threshold >= n - 2
    square_free = n >= 8 and triangle_free and not keep_squares
    counts = dict.fromkeys(MODES, 0)
    graph_count = profile_count = survivors = 0
    examples = {}
    for graph_edges in representatives(n, triangle_free, square_free):
        graph_count += 1
        for profile in orientations(n, graph_edges):
            profile_count += 1
            for mode in MODES:
                bounds = bounds_for(profile, mode, stop_above=threshold)
                if bounds.excludes_above(threshold):
                    counts[mode] += 1
                    if mode not in examples:
                        examples[mode] = refutation(profile, bounds, threshold)
                    break
            else:
                survivors += 1
                if "survivor" not in examples:
                    examples["survivor"] = {
                        "purchases": profile.as_lists(), "equilibrium_interval": bounds.as_dict(),
                    }
    return {
        "n": n, "above": str(threshold), "triangle_pruning": triangle_free,
        "square_pruning": square_free,
        "connected_non_tree_graph_representatives": graph_count,
        "ownership_assignments": profile_count, "first_refuted_by": counts,
        "surviving_ownership_assignments": survivors, "examples": examples,
    }


def make_prompt(result):
    return """# Investigate this network creation game profile

Each player pays alpha times their purchase count plus the sum of graph distances.
An unreachable vertex has infinite distance. Purchases form undirected edges,
and a unilateral deviation replaces a player's whole purchase set.

For each connected deviation, the cost change is a * alpha + b. A Nash
equilibrium requires this expression to be nonnegative.

Use the exact distance and ownership data below to propose a structural lemma.
Prioritize inequalities that apply to min-cycles with arbitrary ownership.
Explain the path replacement and count the affected vertices. Give the
symbolic threshold and identify every extra hypothesis. Give a small profile
that could falsify those hypotheses, or an argument covering every tested case.
Translate a valid candidate into Lean over the archived game definitions and
check it with the kernel. Treat the sample as experimental evidence.

Compare the proposed inequality with Dippel–Vetta (2024), Section 2.2 and
the deviations in Section 3.
https://doi.org/10.4230/LIPIcs.STACS.2024.28

```json
""" + json.dumps(result, indent=2) + "\n```"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    single = commands.add_parser("analyze", help="analyze an ownership profile")
    single.add_argument("profile", help="JSON array of purchased targets per player")
    single.add_argument("--above", type=nonnegative, help="strict threshold, default n")
    single.add_argument("--smt", metavar="PATH", help="write exact QF_LRA constraints")
    exhaustive = commands.add_parser("scan", help="exhaust connected non-tree graphs up to eight vertices")
    exhaustive.add_argument("n", type=int, choices=range(2, 9))
    exhaustive.add_argument("--above", type=nonnegative, help="strict threshold, default n")
    exhaustive.add_argument("--keep-triangles", action="store_true", help="disable short-cycle pruning")
    exhaustive.add_argument("--keep-squares", action="store_true", help="disable square pruning for n = 8")
    replay = commands.add_parser("verify", help="verify a refutation certificate using ordinary BFS")
    replay.add_argument("certificate", help="certificate or complete analyze output")
    prompt = commands.add_parser("prompt", help="prepare an AI research prompt from analyze or scan output")
    prompt.add_argument("result")
    args = parser.parse_args()

    try:
        if args.command == "analyze":
            profile = Profile.from_lists(read_json(args.profile))
            threshold = Fraction(profile.n) if args.above is None else args.above
            write_json(analyze(profile, threshold, args.smt))
        elif args.command == "scan":
            threshold = Fraction(args.n) if args.above is None else args.above
            write_json(scan(args.n, threshold, args.keep_triangles, args.keep_squares))
        elif args.command == "verify":
            data = read_json(args.certificate)
            write_json(verify(data.get("refutation", data)))
        else:
            print(make_prompt(read_json(args.result)))
    except (OSError, KeyError, TypeError, ValueError, argparse.ArgumentTypeError) as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
