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
EXPECTED_ENDPOINT_DEPENDENCIES = {
    TARGETS[0]: set(),
    TARGETS[1]: {
        TARGETS[0],
        "Lax342547.MatchingMinorBound.hadwiger_matching_bound",
        "Lax342547.ChromaticBound.card_le_twice_chromaticNumber_of_indepNum",
    },
    TARGETS[2]: {
        TARGETS[0],
        "Lax342547.MatchingMinorBound.hadwiger_matching_bound",
        "Lax342547.FractionalColoring.fractional_chromatic_lower_bound",
        "Lax342547.FractionalColoring.fractional_chromatic_le_chromatic",
    },
}


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
    statements = {statement["id"] for concept in data["concepts"]
                  for statement in concept["statements"]}
    unresolved = sorted(statements - closed)
    incomplete_proofs = [proof["id"] for proof in data["proofs"]
                         if not set(proof["assumptions"]) <= closed]
    by_conclusion = {}
    for proof in data["proofs"]:
        by_conclusion.setdefault(proof["conclusion"], []).append(proof)
    network_errors = []
    for target, expected in EXPECTED_ENDPOINT_DEPENDENCIES.items():
        for proof in by_conclusion.get(target, []):
            if set(proof["assumptions"]) != expected:
                network_errors.append(f"{proof['id']}: unexpected endpoint dependencies")
    # Resolved Lean references catch qualified and unqualified implementation
    # calls. Using concept statements is what makes the displayed network faithful.
    implementation_ids = {proof["id"] for proof in data["proofs"]}
    for artifact in (ROOT / "proofs" / ".lake" / "build" / "lib" / "lean").rglob("*.ilean"):
        refs = json.loads(artifact.read_text())
        if refs["module"].endswith(".AxiomAudit"):
            continue  # The audit deliberately prints implementation axiom sets.
        for key, reference in refs["references"].items():
            name = json.loads(key).get("c", {}).get("n")
            if name in implementation_ids and reference["usages"]:
                network_errors.append(f"{refs['module']}: calls implementation {name}")
    theorem_concepts = {concept["id"] for concept in data["concepts"]
                        if concept["type"] == "theorem"}
    if theorem_concepts != {"Lax342547.FractionalCounterexample",
                            "Lax342547.MatchingMinorBound"}:
        network_errors.append("Unexpected theorem labels")
    for target in TARGETS:
        print(f"{'CLOSED' if target in closed else 'OPEN'}: {target}")
        if target not in closed:
            proofs = by_conclusion.get(target, [])
            if not proofs:
                print("  No annotated proof of this statement.")
            for proof in proofs:
                unresolved_dependencies = sorted(set(proof["assumptions"]) - closed)
                print(f"  {proof['id']} still depends on: {', '.join(unresolved_dependencies)}")
    if missing or unresolved or incomplete_proofs or network_errors:
        for statement in unresolved:
            print(f"OPEN: {statement}")
        for proof in incomplete_proofs:
            print(f"UNRESOLVED PROOF: {proof}")
        for error in network_errors:
            print(f"NETWORK ERROR: {error}")
        print("Incomplete: do not submit this as a full proof of the counterexample.")
        return 1
    edges = sum(len(proof["assumptions"]) for proof in data["proofs"])
    print(f"All {len(statements)} statements and {len(data['proofs'])} proofs are recursively closed "
          f"({edges} statement dependencies).")
    print("All three targets have the expected Lax dependencies. Review their semantics before submission.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
