"""Independent 64-row truth-table enumeration on all labeled cross-edge graphs."""
import argparse
import json
from itertools import combinations_with_replacement, product

all64 = (1 << 64) - 1
literal = [sum(1 << row for row in range(64) if row >> i & 1) for i in range(6)]
raw = [mask for mask in range(64) if mask & 21 == mask or mask & 42 == mask]
values = {mask: sum(1 << row for row in range(64) if row & mask) for mask in raw}
pairs = [(0, 1), (2, 3), (4, 5)]
cross_edges = [(2 * i, 2 * j + 1) for i, j in product(range(3), repeat=2) if i != j]


def compute(edges, guard=True):
    forbidden = [(1 << (2 * (i // 2) + side)) | (1 << (2 * (j // 2) + side))
                 for i, j in edges if i // 2 != j // 2 for side in (0, 1)]
    menu = [mask for mask in raw if not guard or all(mask & pair != pair for pair in forbidden)]
    required = [1 << ((1 << i) | (1 << j)) for i, j in pairs]
    graph = 0
    for i, j in edges:
        graph |= literal[i] & literal[j]
    wrong = all64 ^ graph
    schedules = models = 0
    example = None
    first = {}
    for p, q in combinations_with_replacement(menu, 2):
        first.setdefault(values[p] & values[q], (p, q))
    for d0, first_ports in first.items():
        ports = {values[k]: (k, 0) for k in menu}
        for k in menu:
            ports.setdefault(values[k] | d0, (k, 1))
        second = {}
        for x, y in combinations_with_replacement(ports, 2):
            second.setdefault(x & y, (ports[x], ports[y]))
        for d1, second_ports in second.items():
            schedules += 1
            terms = [(d0, 'D0'), (d1, 'D1'), (d0 & d1, 'D0D1')]
            terms.extend((gate & vertex, f'D{k}.{chr(65 + i)}')
                         for k, gate in enumerate((d0, d1)) for i, vertex in enumerate(literal))
            clean = [(table, name) for table, name in terms if not table & wrong]
            winners = [next((name for table, name in clean if table & row), None) for row in required]
            if all(winners):
                models += 1
                if example is None:
                    example = {'first': first_ports, 'second': second_ports, 'terms': winners}
    return {'menu': menu, 'schedules': schedules, 'models': models, 'first_witness': example}


if __name__ == '__main__':
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('--all-graphs', action='store_true')
    args = cli.parse_args()
    if args.all_graphs:
        reports = [{'cross': subset, **compute(pairs + [edge for i, edge in enumerate(cross_edges) if subset >> i & 1])}
                   for subset in range(64)]
    else:
        samples = [[], [(0, 3)], [(0, 3), (0, 5)], [(0, 3), (1, 4)]]
        reports = [{'extra_edges': extra, 'guarded': guard, **compute(pairs + extra, guard)}
                   for extra in samples for guard in (False, True)]
    print(json.dumps(reports, indent=None if args.all_graphs else 2))
