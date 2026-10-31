#!/usr/bin/env python3
"""Generate Solution.lean from Challenge.lean: the same theorems, word for word, each proved from the library.

Run from the repository root: python3 scripts/gen_solution.py [--check]
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PROOFS = {
    'theorem3_1': 'ECToBlob.theorem3_1 hN p hp h₁ h₂ hT hmax',
    'theorem4_1': 'ECToBlob.theorem4_1 hN A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ hAB hcover h',
    'theorem8_2': 'ECToBlob.theorem8_2',
    'theorem1': 'TOBQMC.theorem1 hStd hNon hX P G hG T hT hTN hε',
    'theorem1_optimal': 'TOBQMC.theorem1_optimal hStd hNon hX P G hG',
    'theorem2': 'TOBQMC.theorem2 hN hBin hLevel hB hTB Q hQ',
    'consistency': 'TOBQMC.consistency hStd hLevel hNon hBlob hX',
    'theorem4': 'TINNiK.theorem4 hN hX hCor',
}

HEADER = """module

public import ECToBlob
public import External
public import TINNiK
public import TOBQMC

/-!
# The proofs of the statements of record

Each theorem of `Challenge.lean` is restated here, word for word, and proved from the library. This
module also imports the whole library: it is its entry point.
-/

@[expose] public noncomputable section

open Finset MeasureTheory ProbabilityTheory
open scoped Classical

"""


def main():
    chal = (ROOT / 'Challenge.lean').read_text()
    body = chal[chal.index('namespace Challenge'):]
    parts = re.split(r'(by\n  sorry)', body)
    out = []
    names = re.findall(r'^theorem (\S+)', body, flags=re.M)
    i = 0
    for p in parts:
        if p == 'by\n  sorry':
            out.append(PROOFS[names[i]])
            i += 1
        else:
            out.append(p)
    assert i == len(names), (i, names)
    text = HEADER + ''.join(out)
    path = ROOT / 'Solution.lean'
    if '--check' in sys.argv[1:]:
        if path.read_text() != text:
            sys.exit('Solution.lean differs from what scripts/gen_solution.py generates')
        print('Solution.lean is up to date')
    else:
        path.write_text(text)
        print('Solution.lean written')


if __name__ == '__main__':
    main()
