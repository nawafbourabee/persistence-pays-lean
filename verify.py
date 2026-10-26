#!/usr/bin/env python3
"""Compile project modules using a read-only local Lean/mathlib installation."""
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
DEFAULT_REUSE = Path('/Users/nawafbou-rabee/Desktop/quenched-parallel-mcmc/formalization/coupled_jacobi')
REUSE = Path(os.environ.get('PERSISTENCE_LEAN_REUSE', str(DEFAULT_REUSE)))
LEAN = Path(os.environ.get('PERSISTENCE_LEAN_BIN', str(REUSE / '.tools/lean-4.34.0-rc2-darwin_aarch64/bin/lean')))
OUT = ROOT / '.lake/build/lib/lean'
OUT.mkdir(parents=True, exist_ok=True)
env = os.environ.copy()
paths = [OUT]
paths += sorted((REUSE / '.lake/packages').glob('*/.lake/build/lib/lean'))
SLT = Path(os.environ.get('PERSISTENCE_SLT_REUSE',
    str(REUSE / '.tools/lean-stat-learning-theory')))
if (SLT / '.lake/build/lib/lean').is_dir():
    paths.append(SLT / '.lake/build/lib/lean')
env['LEAN_PATH'] = os.pathsep.join(str(p) for p in paths)

requested = [Path(s) for s in sys.argv[1:]] or [Path('PersistencePays.lean'), Path('AxiomAudit.lean')]
requested = [p.relative_to(ROOT) if p.is_absolute() else p for p in requested]
files = []
seen = set()
dependencies = {}

def visit(file):
    if file in seen:
        return
    seen.add(file)
    source = (ROOT / file).read_text()
    dependencies[file] = []
    for name in re.findall(r'^import\s+([A-Za-z0-9_.]+)', source, flags=re.MULTILINE):
        dependency = Path(name.replace('.', '/')).with_suffix('.lean')
        if (ROOT / dependency).is_file():
            dependencies[file].append(dependency)
            visit(dependency)
    files.append(file)

for file in requested:
    visit(file)

rebuilt = set()
for file in files:
    if file.is_absolute():
        file = file.relative_to(ROOT)
    target = OUT / file.with_suffix('.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    if (file not in requested and target.exists()
            and target.stat().st_mtime_ns > (ROOT / file).stat().st_mtime_ns
            and not any(p in rebuilt for p in dependencies[file])
            and all((OUT / p.with_suffix('.olean')).stat().st_mtime_ns < target.stat().st_mtime_ns
                    for p in dependencies[file])):
        continue
    print(f'Checking {file}', flush=True)
    result = subprocess.run([str(LEAN), '-DautoImplicit=false', '-o', str(target), str(file)], cwd=ROOT, env=env)
    if result.returncode:
        target.unlink(missing_ok=True)
        raise SystemExit(result.returncode)
    rebuilt.add(file)
