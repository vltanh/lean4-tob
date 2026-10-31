#!/usr/bin/env python3
"""Generate scripts/Audit.lean from the skill's template, with one `import all` line per module of the libraries.

Run from the repository root: python3 scripts/gen_audit.py
"""
from pathlib import Path
import subprocess, re, os

ROOT = Path(__file__).resolve().parent.parent
TEMPLATE = (ROOT / 'scripts' / 'Audit.lean.in').read_text()

mods = []
for lib in ['Basic', 'External', 'ECToBlob', 'TOBQMC', 'TINNiK']:
    for p in sorted((ROOT / lib).rglob('*.lean')):
        mods.append(str(p.relative_to(ROOT))[:-5].replace('/', '.'))
imports = '\n'.join(f'import all {m}' for m in mods) + '\nimport all Solution'
(ROOT / 'scripts' / 'Audit.lean').write_text(TEMPLATE.replace('-- IMPORTS --', imports))
print(len(mods), 'modules')
