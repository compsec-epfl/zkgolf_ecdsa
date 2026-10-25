#!/usr/bin/env python3
"""Load pinned upstream source locally for audit; no copies are distributed here."""
import argparse
import hashlib
import json
from pathlib import Path
from urllib.request import urlopen

root = Path(__file__).resolve().parent
pin = json.loads((root / "sources.json").read_text())
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--source-tree", type=Path, help="Read source from an existing spartan-backend repository instead of downloading")
args = parser.parse_args()
out = root / "upstream"
out.mkdir(exist_ok=True)
for name, expected in pin["sha256"].items():
    relative = Path(pin["directory"]) / name
    if args.source_tree:
        data = (args.source_tree / relative).read_bytes()
    else:
        url = "https://raw.githubusercontent.com/eid-privacy/spartan-backend/" + pin["commit"] + "/" + relative.as_posix()
        with urlopen(url, timeout=30) as response:
            data = response.read()
    actual = hashlib.sha256(data).hexdigest()
    if actual != expected:
        raise SystemExit(f"source hash mismatch for {name}: {actual} != {expected}")
    if name == "allocated_point.rs":
        text = data.decode()
        old = 's.to_bits_le(cs.namespace(|| "scalar_bits"))?'
        # Two production gadgets and one cfg(test) reference helper.
        if text.count(old) != 3:
            raise SystemExit("unexpected scalar-decomposition call sites")
        data = text.replace(old, 'crate::audit_bits(s, cs.namespace(|| "scalar_bits"))?').encode()
    (out / name).write_bytes(data)
print("Verified pinned source hashes; changed witness generation only. Ready for cargo run.")
