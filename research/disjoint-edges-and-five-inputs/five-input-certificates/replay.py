"""Run from the PEqualNP Lean project with lake env python path/to/replay.py."""
import os
from pathlib import Path
import subprocess
import tempfile

root = Path(__file__).resolve().parent
modules = [
    "Counts", "Structural", "Ends", "LastGate", "Forbidden", "Positions", "Bypass",
    "FinitePlan", "Bridge", "UniformPaths", "Restricted", "Cofactors", "Fanout",
    "Touches", "Charges", "Excluded", "DelayedCharges", "DelayedReads",
    "DelayedExcluded", "Effective", "Absorb", "FirstGate", "RealUse", "Canonical",
    "HeadOptions", "OutputPins", "RoundTwo", "Symmetry", "Orbit", "PostedSeven",
]

modules += ['Envelope', 'Pivotal', 'SATModel', 'SATBridge', 'SATExtract', 'PostedSAT', 'LateShape', 'LateModel', 'KernelReplay', 'LatePins', 'PositionSix', 'StrictLate', 'ModeBridge', 'Cert6', 'Cert5', 'Cert4', 'Lift4']

with tempfile.TemporaryDirectory(prefix="five18096-replay-") as temporary:
    build = Path(temporary)
    paths = [str(build)] + [
        str(Path(path).resolve()) for path in os.environ.get("LEAN_PATH", "").split(os.pathsep) if path
    ]
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(paths))
    env.pop("SIX_CERT_GENERATE", None)
    for module in modules:
        print("Checking " + module, flush=True)
        cmd = [
            "lean", "-j", "1", "-s", "65536", "-M", "6800", "-R", str(root),
            "-o", str(build / (module + ".olean")), str(root / (module + ".lean")),
        ]
        subprocess.run(cmd, env=env, check=True)
