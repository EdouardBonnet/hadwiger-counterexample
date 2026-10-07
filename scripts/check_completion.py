#!/usr/bin/env python3
"""Check the closure of a freshly generated, locally replayed Lax proof network.

This is a completion check, not a replacement for Lean or the Lax inspector.
Run `lax build . --replay` immediately before it. Definitions and statement
semantics still require mathematical review.
"""

import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TARGETS = (
    "Lax342547.Counterexample.arbitrarily_large_small_connected_matching",
    "Lax342547.Counterexample.arbitrarily_large_hadwiger_counterexample",
    "Lax342547.FractionalCounterexample.arbitrarily_large_fractional_counterexample",
)


def closed_statements(proofs):
    """Least fixed point: cycles without an independently closed proof stay open."""
    closed = set()
    changed = True
    while changed:
        changed = False
        for proof in proofs:
            conclusion = proof["conclusion"]
            if conclusion not in closed and set(proof["assumptions"]) <= closed:
                closed.add(conclusion)
                changed = True
    return closed


def main():
    output = ROOT / "build-output.json"
    if not output.is_file():
        print("No inspected build output. Run: lax build . --replay", file=sys.stderr)
        return 2
    data = json.loads(output.read_text())
    if data.get("id") != "lax-342547":
        print("Unexpected submission id in build-output.json.", file=sys.stderr)
        return 2
    if data.get("localValidation", {}).get("replay") is not True:
        print("Kernel replay is missing. Run: lax build . --replay", file=sys.stderr)
        return 2
    # A stale successful output must not authorize submission after source edits.
    inputs = [ROOT / "manifest.yaml", ROOT / "abstract.md", ROOT / "LICENSE"]
    for package in ("concepts", "proofs"):
        inputs.extend([ROOT / package / "lakefile.toml", ROOT / package / "lean-toolchain"])
        inputs.extend((ROOT / package).glob("*.lean"))
        inputs.extend((ROOT / package / ("Lax342547" if package == "concepts" else
                                        "Lax342547Proofs")).rglob("*.lean"))
    if any(p.stat().st_mtime_ns > output.stat().st_mtime_ns for p in inputs):
        print("Source files changed after the inspected build. Run: lax build . --replay",
              file=sys.stderr)
        return 2
    closed = closed_statements(data["proofs"])
    missing = [target for target in TARGETS if target not in closed]
    by_conclusion = {}
    for proof in data["proofs"]:
        by_conclusion.setdefault(proof["conclusion"], []).append(proof)
    for target in TARGETS:
        print(f"{'CLOSED' if target in closed else 'OPEN'}: {target}")
        if target not in closed:
            proofs = by_conclusion.get(target, [])
            if not proofs:
                print("  No annotated proof of this statement.")
            for proof in proofs:
                unresolved = sorted(set(proof["assumptions"]) - closed)
                print(f"  {proof['id']} still depends on: {', '.join(unresolved)}")
    if missing:
        print("Incomplete: do not submit this as a full proof of the counterexample.")
        return 1
    print("All three targets have closed Lax proof networks. Review their semantics before submission.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
