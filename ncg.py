"""Exact deviation calculations for the sum network creation game."""
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from itertools import combinations


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


@dataclass(frozen=True)
class Profile:
    """Bit mask of purchased targets for each player."""

    purchases: tuple[int, ...]

    def __post_init__(self):
        n = len(self.purchases)
        if n < 2:
            raise ValueError("expected at least two players")
        for player, mask in enumerate(self.purchases):
            if type(mask) is not int or not 0 <= mask < 1 << n or mask & (1 << player):
                raise ValueError(f"invalid strategy for player {player}")

    @property
    def n(self):
        return len(self.purchases)

    @classmethod
    def from_lists(cls, purchases):
        if not isinstance(purchases, list):
            raise ValueError("expected a list of lists of purchased targets")
        return cls(tuple(target_mask(targets, len(purchases)) for targets in purchases))

    def as_lists(self):
        return [list(bits(mask)) for mask in self.purchases]

    def incoming(self):
        incoming = [0] * self.n
        for player, mask in enumerate(self.purchases):
            for target in bits(mask):
                incoming[target] |= 1 << player
        return tuple(incoming)

    def adjacency(self):
        return tuple(out | inc for out, inc in zip(self.purchases, self.incoming()))


def target_mask(targets, n):
    if not isinstance(targets, list):
        raise ValueError("expected a list of purchased targets")
    mask = 0
    for target in targets:
        if type(target) is not int or not 0 <= target < n or mask & (1 << target):
            raise ValueError("purchased targets must be distinct player indices")
        mask |= 1 << target
    return mask


def distance_rows(adjacency, source):
    distances = [None] * len(adjacency)
    distances[source] = 0
    queue = [source]
    for vertex in queue:
        for neighbor in bits(adjacency[vertex]):
            if distances[neighbor] is None:
                distances[neighbor] = distances[vertex] + 1
                queue.append(neighbor)
    return distances


def without_vertex(adjacency, player):
    player_bit = 1 << player
    return tuple(0 if v == player else neighbors & ~player_bit
                 for v, neighbors in enumerate(adjacency))


@lru_cache(maxsize=131_072)
def distance_cost(core, own_neighbors, n):
    """BFS initialized with all neighbors of the deviating player."""
    seen = own_neighbors
    frontier = own_neighbors
    total = 0
    depth = 1
    while frontier:
        total += depth * frontier.bit_count()
        next_frontier = 0
        for vertex in bits(frontier):
            next_frontier |= core[vertex]
        frontier = next_frontier & ~seen
        seen |= frontier
        depth += 1
    return total if seen.bit_count() == n - 1 else None


@dataclass(frozen=True)
class Deviation:
    player: int
    targets: int
    a: int
    b: int

    def as_dict(self):
        return {"player": self.player, "targets": list(bits(self.targets)),
                "a": self.a, "b": self.b}


def evaluate_deviation(profile, player, targets):
    """Independently recompute one affine witness using standard BFS."""
    if type(player) is not int or not 0 <= player < profile.n:
        raise ValueError("player index out of range")
    purchases = list(profile.purchases)
    purchases[player] = targets
    modified = Profile(tuple(purchases))
    before = distance_rows(profile.adjacency(), player)
    after = distance_rows(modified.adjacency(), player)
    if None in before:
        raise ValueError("affine deviations require a connected initial graph")
    if None in after:
        return None
    return Deviation(player, targets,
                     targets.bit_count() - profile.purchases[player].bit_count(),
                     sum(after) - sum(before))


MODES = ("delete", "swap", "all")


def strategies(owned, available, mode):
    if mode == "all":
        mask = available
        while mask:
            if mask != owned:
                yield mask
            mask = (mask - 1) & available
        if owned:
            yield 0
        return

    for target in bits(owned):
        reduced = owned ^ (1 << target)
        yield reduced
        if mode == "swap":
            for added in bits(available & ~owned):
                yield reduced | (1 << added)
    if mode == "swap":
        for added in bits(available & ~owned):
            yield owned | (1 << added)


def deviations(profile, mode="all"):
    """Yield connected deviations. All mode omits dominated duplicate buys."""
    if mode not in MODES:
        raise ValueError("unknown deviation mode")
    incoming = profile.incoming()
    adjacency = tuple(out | inc for out, inc in zip(profile.purchases, incoming))
    for player, owned in enumerate(profile.purchases):
        core = without_vertex(adjacency, player)
        before = distance_cost(core, adjacency[player], profile.n)
        if before is None:
            raise ValueError("affine deviations require a connected initial graph")
        # Buying an incoming edge cannot improve a deviation at a positive price.
        available = ((1 << profile.n) - 1) & ~((1 << player) | incoming[player])
        if mode == "all" and owned & incoming[player]:
            yield Deviation(player, owned & available, -(owned & incoming[player]).bit_count(), 0)
        for targets in strategies(owned, available, mode):
            after = distance_cost(core, targets | incoming[player], profile.n)
            if after is not None:
                yield Deviation(player, targets, targets.bit_count() - owned.bit_count(), after - before)


@dataclass
class Bounds:
    lower: Fraction = Fraction(0)
    upper: Fraction | None = None
    lower_witness: Deviation | None = None
    upper_witness: Deviation | None = None
    impossible: Deviation | None = None

    def add(self, deviation):
        a, b = deviation.a, deviation.b
        if a > 0:
            value = Fraction(-b, a)
            if value > self.lower:
                self.lower, self.lower_witness = value, deviation
        elif a < 0:
            value = Fraction(-b, a)
            if self.upper is None or value < self.upper:
                self.upper, self.upper_witness = value, deviation
        elif b < 0:
            self.impossible = deviation

    @property
    def empty(self):
        return self.excludes_above(Fraction(0))

    def excludes_above(self, threshold):
        return self.impossible is not None or (
            self.upper is not None and (self.upper <= threshold or self.upper < self.lower)
        )

    def witnesses(self, threshold):
        if self.impossible is not None:
            return [self.impossible]
        if self.upper <= threshold:
            return [self.upper_witness]
        return [self.lower_witness, self.upper_witness]

    def as_dict(self):
        if self.empty:
            return {"empty": True, "witnesses": [d.as_dict() for d in self.witnesses(Fraction(0))]}
        return {"empty": False, "lower": str(self.lower), "lower_closed": self.lower > 0,
                "upper": None if self.upper is None else str(self.upper),
                "lower_witness": self.lower_witness.as_dict() if self.lower_witness else None,
                "upper_witness": self.upper_witness.as_dict() if self.upper_witness else None}


def bounds_for(profile, mode="all", stop_above=None):
    result = Bounds()
    for deviation in deviations(profile, mode):
        result.add(deviation)
        if stop_above is not None and result.excludes_above(stop_above):
            break
    return result


def cycle_edges(cycle):
    return tuple(zip(cycle, cycle[1:] + cycle[:1]))


def min_cycles(profile):
    """Enumerate simple isometric cycles, once per rotation and reversal."""
    adjacency = profile.adjacency()
    distance = [distance_rows(adjacency, v) for v in range(profile.n)]

    def visit(path, used):
        start, last = path[0], path[-1]
        size = len(path)
        if size > 2 and adjacency[last] & (1 << start):
            if path[1] < last and all(
                distance[path[i]][path[j]] == min(j - i, size - (j - i))
                for i, j in combinations(range(size), 2)
            ):
                yield path
            # Extending a cycle closure would make the closing edge a chord.
            return
        for neighbor in bits(adjacency[last] & ~used):
            if neighbor > start:
                yield from visit(path + (neighbor,), used | (1 << neighbor))

    for start in range(profile.n):
        yield from visit((start,), 1 << start)


def cycle_report(profile, cycle, all_deviations):
    edges = cycle_edges(cycle)
    owned_on_cycle = {v: 0 for v in cycle}
    unique_owners = True
    for a, b in edges:
        a_buys = bool(profile.purchases[a] & (1 << b))
        b_buys = bool(profile.purchases[b] & (1 << a))
        unique_owners &= a_buys != b_buys
        if a_buys:
            owned_on_cycle[a] |= 1 << b
        if b_buys:
            owned_on_cycle[b] |= 1 << a
    bounds = Bounds()
    for d in all_deviations:
        cycle_buys = owned_on_cycle.get(d.player, 0)
        if cycle_buys & ~d.targets:
            bounds.add(d)
    return {"vertices": list(cycle),
            "directed": unique_owners and all(mask.bit_count() == 1 for mask in owned_on_cycle.values()),
            "owners": {v: list(bits(mask)) for v, mask in owned_on_cycle.items()},
            "cycle_edge_removal_bounds": bounds.as_dict()}
