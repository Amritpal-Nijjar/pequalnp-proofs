"""Replay the exact input-row criterion in a configured PequalNP Lean project."""
import argparse
import os
from pathlib import Path
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parent
DEPENDENCIES=('Counts','Structural','Ends','LastGate','Forbidden','Positions','Bypass','FinitePlan','Bridge','UniformPaths')


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--project',required=True,type=Path,help='project lean directory with built imports')
    p.add_argument('--toolchain',required=True,type=Path,help='Lean 4.36.0 toolchain directory')
    opts=p.parse_args()
    project=opts.project.resolve();binary=opts.toolchain.resolve()/'bin'
    lean=binary/('lean.exe' if os.name=='nt' else 'lean')
    assert 'version 4.36.0' in subprocess.check_output([lean,'--version'],text=True)
    with tempfile.TemporaryDirectory() as tmp:
        out=Path(tmp)
        libs=[out,project/'.lake/build/lib/lean',*sorted((project/'.lake/packages').glob('*/.lake/build/lib/lean'))]
        env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,libs)),PATH=str(binary)+os.pathsep+os.environ['PATH'])
        modules=[*DEPENDENCIES,'MaskSlices','MaskCircuit']
        for mod in modules:
            cp=subprocess.run([lean,'-j','1','-M','6500','-R',ROOT,'-o',out/(mod+'.olean'),ROOT/(mod+'.lean')],cwd=ROOT,env=env,check=True)
            print(f'{mod} checked', flush=True)


if __name__=='__main__':
    main()
