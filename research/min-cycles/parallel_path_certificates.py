"""Exclude the remaining parallel degree-two paths at price above n."""
from collections import Counter
from itertools import product

from deviation_certificate_search import exact_cut, row_cache


def words(length, required, backward=()):
    return [tuple(bits) for bits in product((0,1), repeat=length)
            if all(bits[i] for i in required) and all(not bits[i] for i in backward)
            and all(not bits[i] or bits[j] for i in range(length) for j in range(i+2,length))]

def arm_words(length):
    forced = (
        range(1,length) if length >= 4 else
        (1,) if length in (2,3) else ()
    )
    return words(length, forced)

def short_words(length,gap):
    if length==4:
        return words(length,(1,3),(0,2) if gap==0 else ())
    return words(length,())

def candidate_geometries():
    for s,t,r in product(range(1,8),range(1,8),range(1,5)):
        if s>t:
            continue
        n=s+t+r
        gap=min(t,s+r)-s
        if n<9 or r>=3 and gap>=r-2:
            continue
        if t>=5 and (t>min(t,s+r)+3 or 3*(1<<(t-4))>=2*(n-3)):
            continue
        yield s,t,r

def columns(d,a,b):
    size=len(d)
    return (*d,*(min(d[a]+max(0,x), d[b]+max(0,-x)) for x in range(1-size,size)))

def verify():
    cases = 0
    counts = Counter()
    for s, t, r in candidate_geometries():
        size = s + t + r
        root = size - s
        adjacency = [{(i - 1) % size, (i + 1) % size} for i in range(size)]
        pool = row_cache(adjacency, lambda labels: columns(labels, 0, r))
        column_count = 3 * size - 1
        maximum_rows = [
            (0, *(int(j == root) - int(j == v) for j in range(column_count)))
            for v in range(size) if v != root
        ]
        for short, left, right in product(
                short_words(r, min(t, s + r) - s), arm_words(s), arm_words(t)):
            orientation = (*short, *(1 - bit for bit in reversed(right)), *left)
            assert len(orientation) == size
            purchases = [[] for _ in range(size)]
            for i, bit in enumerate(orientation):
                u, v = (i, (i + 1) % size) if bit else ((i + 1) % size, i)
                purchases[u].append(v)
            rows = maximum_rows + [
                row for u, own in enumerate(purchases) for row in pool[u, tuple(sorted(own))]
            ]
            try:
                counts[exact_cut(rows, column_count)] += 1
            except ArithmeticError as error:
                raise ArithmeticError(f"Uncovered {(s, t, r)} and {orientation}") from error
        cases += 1
    print(f"Checked {cases} geometries and {sum(counts.values())} orientations.")
    print(dict(counts))


if __name__ == "__main__":
    verify()
