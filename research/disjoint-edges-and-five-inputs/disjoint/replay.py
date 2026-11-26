"""Rebuild the disjoint-edge results with Lean 4.36.0 and a prebuilt project."""
import argparse
from contextlib import nullcontext
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
PIN = '8ad50440ecd2520a5e3c727f7b1a19f079cac700'
TARGETS = ('DisjointAudit',)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', required=True, type=Path, help='prebuilt pequalnp-proofs/lean directory')
    parser.add_argument('--research-repo', required=True, type=Path, help='Git clone containing the pinned Kapre revision')
    parser.add_argument('--toolchain', required=True, type=Path, help='Lean 4.36.0 directory containing bin')
    parser.add_argument('--prebuilt', type=Path, help='optional already-checked research imports')
    parser.add_argument('--build-dir', type=Path, help='keep intermediate objects in a new local directory')
    parser.add_argument('--with-touching', action='store_true', help='also link the published touching-case proof')
    parser.add_argument('--check-objects', action='store_true', help='run the separate leanchecker on the new certificate and conclusions')
    parser.add_argument('--time-limit', type=int, help='optional wall-clock limit in seconds for the build')
    args = parser.parse_args()
    end = time.monotonic() + args.time_limit if args.time_limit else None

    def remaining():
        if end is None:
            return None
        if time.monotonic() >= end:
            raise TimeoutError('Replay time limit reached')
        return end - time.monotonic()
    project, repo, binary = args.project.resolve(), args.research_repo.resolve(), args.toolchain.resolve() / 'bin'
    local = {p.stem: p for p in (HERE / 'src').glob('*.lean')}
    local['AllThree'] = HERE / 'integration/AllThree.lean'
    listed = subprocess.check_output(['git', '-C', repo, 'ls-tree', '-r', '--name-only', PIN, 'research/L-meta-17625'], text=True).splitlines()
    remote = {Path(p).stem: p for p in listed if p.endswith('.lean')}
    if len(remote) != sum(p.endswith('.lean') for p in listed):
        raise ValueError('Ambiguous research module names')
    cache = args.prebuilt.resolve() if args.prebuilt else None
    libs = [project / '.lake/build/lib/lean', *sorted((project / '.lake/packages').glob('*/.lake/build/lib/lean'))]
    if not (libs[0] / 'PEqualNP').is_dir():
        parser.error('project Lean imports have to be built first')
    env = os.environ.copy()
    env.update(LEAN_NUM_THREADS='1', SIX_CERT_GENERATE='0')
    suffix = '.exe' if os.name == 'nt' else ''
    lean, checker = (binary / (name + suffix) for name in ('lean', 'leanchecker'))
    version = subprocess.check_output([lean, '--version'], text=True).strip()
    if not version.startswith('Lean (version 4.36.0,'):
        parser.error(version)
    print(version, flush=True)
    if args.build_dir:
        scratch_dir = args.build_dir.resolve()
        scratch_dir.mkdir(parents=True, exist_ok=False)
        location = nullcontext(scratch_dir)
    else:
        location = tempfile.TemporaryDirectory(prefix='read17625-disjoint-')
    with location as tmp:
        scratch = Path(tmp).resolve()
        certs = scratch / 'certificates'
        certs.mkdir()
        env['LEAN_PATH'] = os.pathsep.join(map(str, [scratch, *([cache] if cache else []), *libs]))
        done = set()

        def blob(path):
            return subprocess.check_output(['git', '-C', repo, 'show', PIN + ':' + path])

        def build(name):
            if name in done:
                return
            done.add(name)
            if name not in local and cache and (cache / (name + '.olean')).is_file():
                return
            staged = scratch / (name + '.lean')
            if name in local:
                shutil.copyfile(local[name], staged)
                cert = HERE / 'src/certificates' / (name + '.lrat')
                if cert.is_file():
                    shutil.copyfile(cert, certs / cert.name)
            else:
                source = remote[name]
                staged.write_bytes(blob(source))
                cert = str(Path(source).parent.as_posix()) + '/certificates/' + name + '.lrat'
                if cert in listed:
                    (certs / (name + '.lrat')).write_bytes(blob(cert))
            for line in staged.read_text(encoding='utf-8-sig').splitlines():
                if line.startswith(('import ', 'public import ')):
                    for dep in line.split('import ', 1)[1].split():
                        if dep in local or dep in remote:
                            build(dep)
            print('Building', name, flush=True)
            subprocess.run([lean, '-j', '1', '-R', scratch, '-o', scratch / (name + '.olean'), staged],
                           env=env, cwd=scratch, check=True, timeout=remaining())

        targets = [*TARGETS, *(['AllThree'] if args.with_touching else [])]
        for name in targets:
            build(name)
        if args.check_objects:
            for name in ['SixExclusion', 'SixBridge', 'DisjointBound', *targets]:
                subprocess.run([checker, '-v', name], env=env, cwd=scratch, check=True, timeout=remaining())
        print('Verified', ', '.join(targets), flush=True)


if __name__ == '__main__':
    main()
