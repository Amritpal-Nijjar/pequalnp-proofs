"""Construct a Lean type compatibility check from Kapre's verbatim published signature."""
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parent
repo = Path(sys.argv[1]).resolve()
pin = '8ad50440ecd2520a5e3c727f7b1a19f079cac700'
path = 'research/L-meta-17625/overlap-next/disjoint/projection/TwoTouching.lean'
source = subprocess.check_output(['git', '-C', repo, 'show', pin + ':' + path]).decode()
name = 'theorem failure_requires_three_disjoint '
signature = source.split(name, 1)[1].split(' :=', 1)[0].replace(' :\n    ∀ z', ',\n    ∀ z')
wrapper = (root / 'integration/AllThree.lean').read_text(encoding='utf8')
wrapper = wrapper.replace('import TwoTouching\n', '').replace('theorem three_edges ',
    'abbrev PublishedFailureType (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Prop :=\n  ∀ ' + signature + '\n\n' +
    'theorem three_from_pinned_signature (published : PublishedFailureType G C) ')
wrapper = wrapper.replace('DisjointEdgeBound.failure_requires_three_disjoint', 'published')
wrapper = wrapper.replace('#print axioms three_edges', '#print axioms three_from_pinned_signature')
(root / 'src/PinnedSignature.lean').write_text(wrapper, encoding='utf8')
