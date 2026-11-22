"""Verify two octagon families stable under all purchases confined to the cycle."""
import argparse
from dataclasses import dataclass
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from ncg import Profile, distance_rows, evaluate_deviation


HUBS_191_185 = (
    ((3,2,1,0,1,2,3,4), 153, 35),
    ((2,1,0,1,2,1,2,3), 91, 19),
    ((2,1,0,1,2,3,3,3), 80, 24),
    ((2,1,2,1,0,1,2,3), 91, 19),
    ((1,0,1,2,1,0,1,2), 137, 27),
    ((1,0,1,2,3,3,2,2), 131, 26),
    ((1,0,1,2,3,4,3,2), 2, 6),
    ((3,3,2,1,0,1,2,3), 80, 24),
    ((1,1,0,1,0,1,1,0), 99, 22),
    ((3,4,3,2,1,0,1,2), 2, 6),
    ((1,2,1,2,1,2,1,0), 79, 11),
    ((2,3,3,2,1,0,1,2), 131, 26),
    ((1,2,2,1,2,2,1,0), 303, 62),
    ((1,2,3,4,3,2,1,0), 248, 63),
)

HUBS_57_56 = (
    ((3, 2, 1, 0, 1, 2, 3, 4), 202, 13),
    ((2, 1, 0, 1, 2, 1, 2, 3), 284, 16),
    ((2, 1, 0, 1, 2, 3, 3, 3), 1, 3),
    ((2, 1, 2, 2, 1, 0, 1, 2), 190, 11),
    ((1, 0, 1, 2, 2, 1, 2, 2), 80, 6),
    ((1, 0, 1, 2, 3, 3, 2, 2), 144, 5),
    ((1, 0, 1, 2, 3, 4, 3, 2), 122, 10),
    ((3, 3, 2, 1, 0, 1, 2, 3), 360, 23),
    ((2, 2, 1, 2, 1, 0, 1, 1), 45, 2),
    ((1, 1, 0, 1, 2, 2, 1, 0), 272, 15),
    ((2, 2, 2, 1, 0, 1, 2, 3), 40, 3),
    ((2, 3, 3, 2, 1, 0, 1, 1), 33, 4),
    ((1, 2, 2, 1, 2, 2, 1, 0), 276, 17),
    ((1, 2, 3, 3, 2, 2, 1, 0), 537, 24),
    ((1, 2, 3, 3, 3, 2, 1, 0), 29, 7),
    ((1, 2, 3, 4, 3, 2, 1, 0), 64, 9),
)
@dataclass(frozen=True)
class Family:
    hubs: tuple[tuple[tuple[int, ...], int, int], ...]
    initial_order: int
    order_increment: int
    price_increment: int
    outside_link: tuple[int, int]
    initial_saving: int
    saving_increment: int


FAMILIES = {
    "00001101": Family(HUBS_57_56, 2913, 168, 171, (2, 196), 1964, 45),
    "00011101": Family(HUBS_191_185, 1820, 370, 382, (0, 172), 335, 52),
}
CYCLE_SIZE = 8
CYCLE_MASK = (1 << CYCLE_SIZE) - 1


def example(batch, orientation="00011101"):
    purchases = [[] for _ in range(CYCLE_SIZE)]
    for vertex, direction in enumerate(orientation):
        following = (vertex + 1) % CYCLE_SIZE
        buyer, target = (vertex, following) if direction == "0" else (following, vertex)
        purchases[buyer].append(target)
    leaf_counts = []
    for levels, initial_leaves, batch_leaves in FAMILIES[orientation].hubs:
        hub = len(purchases)
        purchases.append([])
        leaf_counts.append((hub, initial_leaves + batch * batch_leaves))
        for vertex, level in enumerate(levels):
            if level > min(levels[(vertex - 1) % CYCLE_SIZE], levels[(vertex + 1) % CYCLE_SIZE]):
                continue
            previous = vertex
            for _ in range(6 + level):
                target = len(purchases)
                purchases.append([])
                purchases[previous].append(target)
                previous = target
            purchases[previous].append(hub)
    for hub, count in leaf_counts:
        for _ in range(count):
            purchases[hub].append(len(purchases))
            purchases.append([])
    return Profile.from_lists(purchases)


def cost_change(profile, price, buyer, targets):
    deviation = evaluate_deviation(profile, buyer, targets)
    return None if deviation is None else deviation.a * price + deviation.b


def verify(orientation="00011101"):
    family = FAMILIES[orientation]
    base, next_batch = example(0, orientation), example(1, orientation)
    assert base.n == family.initial_order and next_batch.n - base.n == family.order_increment
    price = base.n + 1
    for profile in (base, next_batch):
        adjacency = profile.adjacency()
        for u in range(CYCLE_SIZE):
            actual = distance_rows(adjacency, u)
            for v in range(CYCLE_SIZE):
                assert actual[v] == min(abs(u - v), CYCLE_SIZE - abs(u - v))
    count = 0
    min_change = None
    min_slope = None
    for buyer in range(CYCLE_SIZE):
        remaining = base.purchases[buyer] & ~CYCLE_MASK
        assert remaining == next_batch.purchases[buyer] & ~CYCLE_MASK
        for targets in range(CYCLE_MASK + 1):
            if targets & (1 << buyer):
                continue
            count += 1
            change = cost_change(base, price, buyer, remaining | targets)
            later_change = cost_change(next_batch, price + family.price_increment, buyer, remaining | targets)
            if change is None:
                assert later_change is None
                continue
            assert later_change is not None
            # Each extra leaf has the distance change of its hub. All changes are affine.
            slope = later_change - change
            assert change >= 0 and slope >= 0
            if remaining | targets != base.purchases[buyer]:
                min_change = change if min_change is None else min(min_change, change)
                min_slope = slope if min_slope is None else min(min_slope, slope)

    buyer, hub = family.outside_link
    target_set = base.purchases[buyer] | (1 << hub)
    reduction = -cost_change(base, price, buyer, target_set)
    next_reduction = -cost_change(next_batch, price + family.price_increment, buyer, target_set)
    assert count == 1024
    assert reduction == family.initial_saving and next_reduction - reduction == family.saving_increment
    return {
        "players": base.n,
        "alpha": price,
        "cycle_purchase_strategies": count,
        "minimum_change_for_nontrivial_cycle_move": min_change,
        "minimum_cycle_move_slope": min_slope,
        "outside_buyer": buyer,
        "outside_target": hub,
        "outside_cost_reduction": reduction,
        "players_per_extra_batch": family.order_increment,
        "alpha_increase_per_batch": family.price_increment,
        "outside_cost_reduction_increase_per_batch": next_reduction - reduction,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("orientation", choices=FAMILIES, nargs="?", default="00011101")
    print(json.dumps(verify(parser.parse_args().orientation), indent=2))
