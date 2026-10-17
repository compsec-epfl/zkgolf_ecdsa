#!/usr/bin/env python3
"""Fail closed on missing audit roots or axioms outside the challenge policy."""
import re
import subprocess
from pathlib import Path

standard = {'propext', 'Quot.sound', 'Classical.choice'}
for source, allowed in [
    ('Tests/Axioms.lean', standard),
]:
    expected = set(re.findall(r'^#print axioms (\S+)$', Path(source).read_text(), re.M))
    result = subprocess.run(
        ['lake', 'env', 'lean', source], text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True,
    )
    reports = {name: set(filter(None, map(str.strip, axioms.split(','))))
               for name, axioms in re.findall(
                   r"'([^']+)' depends on axioms: \[([^\]]*)\]", result.stdout)}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", result.stdout):
        reports[name] = set()
    if reports.keys() != expected:
        print(result.stdout)
        raise SystemExit(f'{source}: missing or unexpected axiom audit reports')
    for name, axioms in reports.items():
        if unexpected := axioms - allowed:
            raise SystemExit(f'{name}: forbidden axioms: {sorted(unexpected)}')
    print(f'{source}: {len(reports)} roots passed the permitted-axiom audit')
