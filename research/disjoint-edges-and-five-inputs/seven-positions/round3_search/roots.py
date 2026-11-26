"""Generate the five-gate monotone prefix banks for both remaining NOT positions."""
from array import array
from datetime import datetime, timezone
from hashlib import sha256
import argparse
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent/'paired2_gpu'))
from run_search import physical
from run_live import prefix_debt
from slot_prefixes import extend
from wide_positions import state_key, pack_prefix, unpack_prefix


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--deadline', required=True)
    p.add_argument('--output', type=Path, default=HERE)
    args = p.parse_args()
    until = datetime.fromisoformat(args.deadline.replace('Z','+00:00')).timestamp()
    states = {state_key([]): b''}
    stages = []
    for depth in range(1, 6):
        following = {}
        transitions = 0
        for number, code in enumerate(states.values()):
            if number % 64 == 0 and time.time() >= until - 2:
                raise TimeoutError('Root generation reached its cap')
            for gates in extend(unpack_prefix(code)):
                transitions += 1
                key = state_key(gates)
                if key not in following:
                    following[key] = pack_prefix(gates)
        states = following
        stages.append([depth, transitions, len(states)])
        print(stages[-1], flush=True)
    assert [v[2] for v in stages] == [8, 81, 1002, 13790, 207536]
    packed = sorted(states.values())
    records = array('I')
    for code in packed:
        gates = unpack_prefix(code)
        records.extend(physical(gates))
        records.append(prefix_debt(gates))
    assert records.itemsize == 4 and sys.byteorder == 'little'
    folder = args.output
    codes, banks = b''.join(packed), records.tobytes()
    (folder/'roots_codes.bin').write_bytes(codes)
    (folder/'roots_banks.bin').write_bytes(banks)
    (folder/'roots.json').write_text(json.dumps({'stages':stages,'roots':len(states),
        'codes_sha256':sha256(codes).hexdigest(),'banks_sha256':sha256(banks).hexdigest(),
        'finished':datetime.now(timezone.utc).isoformat(timespec='seconds')}, indent=2), encoding='utf-8')


if __name__ == '__main__':
    main()
