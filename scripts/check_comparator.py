#!/usr/bin/env python3
"""Local compatibility tests on self-authored fixtures, NOT a circuit solution.
Uses upstream's unsandboxed development shim; never run untrusted submissions.
Pass a checkout of leanprover/comparator at the revision below, built with
ELAN_TOOLCHAIN=leanprover/lean4:v4.34.0 lake build comparator lean4export.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

REV = '51491237b1d2f96cca203af9c34bced6fe38e0d8'
EXPORT_REV = 'af5aa64bb914c3c2c781f378088dbd38acf4f804'
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('comparator_checkout', type=Path)
a = p.parse_args()
root = Path(__file__).resolve().parents[1]
checkout = a.comparator_checkout.resolve()
for path, revision in [(checkout, REV), (checkout / '.lake/packages/lean4export', EXPORT_REV)]:
    actual = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
    if actual != revision:
        raise SystemExit(f'Wrong revision at {path}: {actual}')
env = dict(os.environ,
    COMPARATOR_LANDRUN=str(checkout / 'scripts/fake-landrun.sh'),
    COMPARATOR_LEAN4EXPORT=str(checkout / '.lake/packages/lean4export/.lake/build/bin/lean4export'))
base = json.loads((root / 'configs/ECDSA_P256_Digest.json').read_text())
smoke = dict(base, challenge_module='Tests.Comparator.Challenge',
             theorem_names=['ComparatorSmoke.relation'], definition_names=[])
cases = [
    ('valid-relation', dict(smoke, solution_module='Tests.Comparator.Valid'), True,
     'Lean default kernel accepts the solution'),
    ('unfinished-proof', dict(smoke, solution_module='Tests.Comparator.Invalid'), False,
     "Illegal axiom detected: 'sorryAx'"),
    ('changed-statement', dict(smoke, solution_module='Tests.Comparator.Mismatch'), False,
     'Challenge and solution theorem statement do not match'),
    ('challenge-template-is-not-solution', dict(base, solution_module=base['challenge_module']), False,
     "Illegal axiom detected: 'sorryAx'"),
]
logs = root / 'dist/comparator-checks'
logs.mkdir(parents=True, exist_ok=True)
results = []
with tempfile.TemporaryDirectory(prefix='ecdsa-comparator-') as temp:
    for name, config, accept, marker in cases:
        file = Path(temp) / f'{name}.json'
        file.write_text(json.dumps(config))
        run = subprocess.run(['lake', 'env', str(checkout / '.lake/build/bin/comparator'), str(file)],
            cwd=root, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=1200)
        (logs / f'{name}.log').write_text(run.stdout)
        ok = (run.returncode == 0) == accept and marker in run.stdout
        results.append({'case': name, 'passed': ok, 'exit_code': run.returncode})
        print(f'{name}: {"PASS" if ok else "FAIL"}', flush=True)
        if not ok:
            print(run.stdout[-4000:])
            raise SystemExit(1)
(logs / 'results.json').write_text(json.dumps({
    'comparator_revision': REV, 'lean4export_revision': EXPORT_REV,
    'toolchain': (root / 'lean-toolchain').read_text().strip(),
    'scope': 'local development shim; no sandbox, no full circuit proof',
    'trusted_relation': 'Challenge.Specs.ECDSAP256.Spec',
    'trusted_wrapper_sha256': hashlib.sha256((root / 'Challenge/Specs/ECDSAP256.lean').read_bytes()).hexdigest(),
    'circuit_field': 'P-256 base field',
    'upstream_relation': 'ValidEcdsaWitness',
    'cases': results}, indent=2) + '\n')
