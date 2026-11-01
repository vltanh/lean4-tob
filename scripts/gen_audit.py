#!/usr/bin/env python3
"""Generate scripts/Audit.lean from its template, with one `import all` line per module.

The modules are those of the libraries below and of the library `Phylogenetics`, whose proofs the audit
must see too: the module system hides them from a plain `import`. The template lists no module.
`Gusfield2007`, the statement files of `AllmanEtAl2023`, and the directories of `External` that serve those
two papers are left out while they are being written.

Run from the repository root: python3 scripts/gen_audit.py [--check]
"""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
TEMPLATE = (ROOT / 'scripts' / 'Audit.lean.in').read_text()
PROJECT_LIBRARIES = ['Basic', 'External/AllmanBanosRhodes2019', 'External/AneEtAl2024', 'External/HuberEtAl2025',
                     'External/MitchellAllmanRhodes2019', 'External/Rhodes2020', 'ECToBlob', 'TOBQMC', 'TINNiK']
ALLMAN = ['SubgraphBlobs', 'CutOrder', 'CycleLemma', 'Reduction', 'Basic', 'Theorem1', 'Corollary1']


def library_dir():
    """The checkout of the library `Phylogenetics`, a package of Lake."""
    return ROOT / '.lake' / 'packages' / 'Phylogenetics'


def modules(root, library):
    return [str(p.relative_to(root))[:-5].replace('/', '.') for p in sorted((root / library).rglob('*.lean'))]


def main():
    mods = [m for lib in PROJECT_LIBRARIES for m in modules(ROOT / 'src', lib)] + [f'AllmanEtAl2023.{m}' for m in ALLMAN]
    mods += modules(library_dir(), 'Phylogenetics')
    imports = '\n'.join(f'import all {m}' for m in mods) + '\nimport all MainResults'
    text = TEMPLATE.replace('-- IMPORTS --', imports)
    path = ROOT / 'scripts' / 'Audit.lean'
    if '--check' in sys.argv[1:]:
        if path.read_text() != text:
            sys.exit('scripts/Audit.lean differs from what scripts/gen_audit.py generates')
        print(len(mods), 'modules: scripts/Audit.lean is up to date')
    else:
        path.write_text(text)
        print(len(mods), 'modules')


if __name__ == '__main__':
    main()
