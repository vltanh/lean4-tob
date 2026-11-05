#!/usr/bin/env python3
"""Check the imports of `src/` against the units of `scripts/layers.toml`.

Every module must belong to one unit, every import of a module of this project must stay in its unit or go
to a unit that its unit lists in `imports`, and the units must form no cycle. Declared imports that no
module uses are reported, without failing.

Run from the repository root: python3 scripts/check_layers.py [--graph]
With --graph, print the units and the units each one imports, lowest first.
"""
import re
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / 'src'
IMPORT = re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)', re.M)


def module_name(path):
    return '.'.join(path.relative_to(SRC).with_suffix('').parts)


def main():
    units = tomllib.loads((ROOT / 'scripts' / 'layers.toml').read_text())['units']
    errors = []
    for name, unit in units.items():
        for dep in unit['imports']:
            if dep not in units:
                errors.append(f'{name}: imports the unknown unit {dep}')
    owner = {}
    for name, unit in units.items():
        for p in unit['paths']:
            if not (SRC / p).exists():
                errors.append(f'{name}: no {SRC.name}/{p}')
            owner[p.removesuffix('.lean')] = name

    def unit_of(module):
        parts = module.split('.')
        for k in range(len(parts), 0, -1):
            u = owner.get('/'.join(parts[:k]))
            if u:
                return u
        return None

    modules = {module_name(p): p for p in sorted(SRC.rglob('*.lean'))}
    roots = {m.split('.')[0] for m in modules}
    used = set()
    for module, path in modules.items():
        u = unit_of(module)
        if u is None:
            errors.append(f'{path.relative_to(ROOT)}: in no unit of scripts/layers.toml')
            continue
        for imp in IMPORT.findall(path.read_text()):
            if imp.split('.')[0] not in roots:
                continue
            v = unit_of(imp)
            if v is None or imp not in modules:
                errors.append(f'{path.relative_to(ROOT)}: imports {imp}, which is not a module of this project')
            elif v != u:
                used.add((u, v))
                if v not in units[u]['imports']:
                    errors.append(f'{path.relative_to(ROOT)}: imports {imp}, but {u} may not import {v}')

    # The units form no cycle: order them, lowest first.
    order, state = [], {}

    def visit(name, stack):
        if state.get(name) == 'done':
            return
        if state.get(name) == 'open':
            errors.append('the units form a cycle: ' + ' -> '.join(stack[stack.index(name):] + [name]))
            return
        state[name] = 'open'
        for dep in units[name]['imports']:
            if dep in units:
                visit(dep, stack + [name])
        state[name] = 'done'
        order.append(name)

    for name in units:
        visit(name, [])

    for name, unit in units.items():
        for dep in unit['imports']:
            if (name, dep) not in used:
                print(f'note: {name} may import {dep}, but no module does', file=sys.stderr)
    if '--graph' in sys.argv:
        for name in order:
            print(f"{name}: {', '.join(units[name]['imports']) or '-'}")
    if errors:
        print('\n'.join(errors), file=sys.stderr)
        sys.exit(1)
    print(f'{len(modules)} modules in {len(units)} units, no import outside scripts/layers.toml, no cycle')


if __name__ == '__main__':
    main()
