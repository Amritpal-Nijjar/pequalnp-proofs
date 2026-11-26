"""Run from the pinned project's lean directory using lake env python3 /path/to/replay.py."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile


def main():
    lean = shutil.which('lean')
    checker = shutil.which('leanchecker')
    if not lean or not checker:
        raise SystemExit('Run under lake env with Lean 4.36.0.')
    source = Path(__file__).resolve().with_name('FiveByFive.lean')
    libraries = [str(Path(p).resolve()) for p in os.environ.get('LEAN_PATH', '').split(os.pathsep) if p]
    statement = '''import FiveByFive

example : ∀ (A : Fin 5 → Fin 5 → Bool) (s : ℕ),
    PEqualNP.Represents.RepSizeAtMost (fun i j => !A i j) s →
    PEqualNP.Represents.RepSizeAtMost A (s + 10) := FiveExact.exact

#print axioms FiveExact.exact
'''
    with tempfile.TemporaryDirectory() as temp:
        build = Path(temp)
        env = dict(os.environ, LEAN_PATH=os.pathsep.join([temp, *libraries]), LEAN_NUM_THREADS='2')
        shutil.copyfile(source, build / source.name)
        (build / 'ExactStatement.lean').write_text(statement, encoding='utf-8')
        subprocess.run([lean, '-j', '2', '-R', '.', '-o', 'FiveByFive.olean', source.name],
                       cwd=build, env=env, check=True)
        result = subprocess.run([lean, '-j', '2', '-R', '.', 'ExactStatement.lean'],
                                cwd=build, env=env, check=True, stdout=subprocess.PIPE, encoding='utf-8')
        print(result.stdout.strip(), flush=True)
        expected = "'FiveExact.exact' depends on axioms: [propext, Classical.choice, Quot.sound]"
        if result.stdout.strip() != expected:
            raise SystemExit('The axiom report differs from the pinned replay.')
        subprocess.run([checker, '-v', 'FiveByFive'], cwd=build, env=env, check=True)
    print('The five-by-five proof passed kernel replay.')


if __name__ == '__main__':
    main()
