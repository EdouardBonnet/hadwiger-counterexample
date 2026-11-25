#!/usr/bin/env python3
"""Compile every new finite lemma and audit its transitive axiom dependencies.

This checks the new lemmas, not adoption of the proposals by the final theorem.
Run from any directory. Only the pinned local Lean/mathlib environment is used.
"""
import hashlib
import json
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "proofs"
DIRECTORY = PROOFS / "Lax793645Proofs" / "Simplifications"
NAMESPACE = "Lax793645Proofs.Simplifications"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
# Archive concepts are statement placeholders. Resolve each to its separately
# compiled annotated proof, rejecting cycles and any unlisted axiom.
CLOSED = {"Lax793645." + name: "Lax793645Proofs." + name for name in (
    "ResidualRegularity.common_partition", "AdaptivePartitions.common_partition",
    "OverlapTransfer.finite_transfer", "OverlapTransfer.clipped_transfer",
    "FiniteScores.large_score_probability", "FiniteScores.squared_score_probability",
)}


def declarations_in(code):
    """Track namespace and section scopes, including upstream extensions."""
    scopes = []
    for line in code.splitlines():
        start = re.fullmatch(r"\s*namespace\s+([^\s]+)\s*", line)
        if start:
            scopes.append(start.group(1))
            continue
        if re.fullmatch(r"\s*(?:noncomputable\s+)?section(?:\s+\S+)?\s*", line):
            scopes.append(None)
            continue
        if re.fullmatch(r"\s*end(?:\s+\S+)?\s*", line):
            assert scopes, line
            scopes.pop()
            continue
        theorem = re.match(r"^theorem\s+([^\s({:]+)", line)
        if theorem:
            yield ".".join([*(scope for scope in scopes if scope), theorem.group(1)])
    assert not scopes, scopes


def run(args):
    result = subprocess.run(args, cwd=PROOFS, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout + result.stderr


def main():
    paths = sorted(DIRECTORY.glob("*.lean"))
    assert paths, "No simplification modules"
    declarations = []
    for path in paths:
        code = path.read_text()
        assert not re.search(r"\b(sorry|admit|native_decide)\b", code), path
        assert not re.search(r"^\s*(axiom|unsafe)\b", code, re.M), path
        declarations.extend(declarations_in(code))
    modules = [NAMESPACE + "." + path.stem for path in paths]
    proof_modules = sorted({name.rsplit(".", 1)[0] for name in CLOSED.values()})
    print(f"Compiling {len(modules)} modules...", flush=True)
    build_log = run(["lake", "build", *modules, *proof_modules])
    print(build_log, end="", flush=True)
    audit = "\n".join([*("import " + m for m in modules + proof_modules),
                       *("#print axioms " + d for d in declarations + list(CLOSED.values()))]) + "\n"
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as file:
        file.write(audit)
        audit_path = Path(file.name)
    try:
        output = run(["lake", "env", "lean", str(audit_path)])
    finally:
        audit_path.unlink()
    checked = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output):
        dependencies = {a.strip() for a in axioms.split(",") if a.strip()}
        checked[name] = sorted(dependencies)
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        checked[name] = []
    assert set(checked) == set(declarations) | set(CLOSED.values()), output
    raw = dict(checked)
    def expand(axioms, stack=()):
        result = set()
        for axiom in axioms:
            if axiom in ALLOWED:
                result.add(axiom)
            else:
                assert axiom in CLOSED, (axiom, stack)
                assert axiom not in stack, ("Circular statement proof", axiom, stack)
                result |= expand(raw[CLOSED[axiom]], (*stack, axiom))
        return result
    # Check each proof too, even if an individual audit target does not need it.
    for name in CLOSED.values():
        expand(raw[name])
    checked = {name: sorted(expand(raw[name])) for name in declarations}
    report = {
        "scope": "Finite verification lemmas; no claim of full construction integration",
        "lean_version": run(["lake", "env", "lean", "--version"]).strip(),
        "modules": modules,
        "theorems": checked,
        "raw_axioms": raw,
        "statement_proofs": CLOSED,
        "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in paths},
    }
    target = ROOT / "references" / "further-simplifications-audit.json"
    target.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(f"CHECKED: {len(checked)} theorems in {len(modules)} modules.")
    print("Only propext, Classical.choice, and Quot.sound remain after resolving checked statement proofs.")
    print("Full integration of the five proposals is not asserted by this audit.")


if __name__ == "__main__":
    main()
