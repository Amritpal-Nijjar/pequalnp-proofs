"""Cross-check layered canonicalization against an unmerged enumeration at four gates."""
import json
from pathlib import Path

from slot_prefixes import extend, groups
from wide_positions import add_nots, state_key


def validate(position):
    direct, raw_count = groups(position)
    expected = {state_key(prefix) for prefix in direct.values()}
    layer = {state_key([]): []}
    for index in range(4):
        following = {}
        for prefix in layer.values():
            for candidate in (add_nots(prefix) if index == position else extend(prefix)):
                following.setdefault(state_key(candidate), candidate)
        layer = following
    if expected != layer.keys():
        raise ValueError(f'Different reachable wire banks at NOT position {position}')
    return {'position_zero_based': position, 'four_gate_prefixes': raw_count, 'matching_classes': len(expected)}


if __name__ == '__main__':
    checks = [validate(position) for position in (1, 2, 3)]
    dest = Path(__file__).with_name('prefix_crosscheck.json')
    dest.write_text(json.dumps(checks, indent=2) + '\n', encoding='utf-8')
    print(checks)
