#!/usr/bin/env python3
"""Check the numbered manuscript against the archived cards and PDF destinations."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "paper"
RESULTS = "lemma|theorem|proposition|corollary|definition"
TOKEN = re.compile(
    r"^\s*% lax (?:(?:begin (?P<mark>\S+))|(?P<close>end))\s*$"
    r"|\\begin\{(?P<begin>" + RESULTS + r"|proof)\}(?:\[(?P<caption>[^\]]*)\])?"
    r"|\\end\{(?P<end>" + RESULTS + r"|proof)\}"
    r"|\\label\{(?P<label>[^}]+)\}|\\input\{(?P<input>[^}]+)\}",
    re.MULTILINE,
)


def read_paper(concepts, proofs):
    statements, proof_marks, marks, files = {}, {}, Counter(), set()
    named_references = []

    def read(path):
        assert path not in files, f"Paper includes {path.name} twice"
        files.add(path)
        topic = current = last = None
        stack = []
        # TeX comments can contain example markup. Only a complete marker line is active.
        lines = [line if line.strip().startswith("% lax ") else re.split(r"(?<!\\)%", line)[0]
                 for line in path.read_text().splitlines()]
        source = "\n".join(lines)
        named_references.extend(re.findall(
            r"\b(Lemma|Theorem|Proposition|Corollary|Definition)~\\ref\{([^}]+)\}", source
        ))
        for match in TOKEN.finditer(source):
            fields = match.groupdict()
            if fields["mark"]:
                card = fields["mark"]
                assert card in concepts or card in proofs, f"Unresolved card {card}"
                stack.append(card)
                marks[card] += 1
            elif fields["close"]:
                assert stack, f"Unmatched closing mark in {path.name}"
                stack.pop()
            elif fields["input"]:
                child = PAPER / fields["input"]
                read(child if child.suffix else child.with_suffix(".tex"))
            elif fields["begin"]:
                assert current is None
                current = fields["begin"]
                if current == "proof":
                    label = re.search(r"\\(?:Cref|ref)\{([^}]+)\}", fields["caption"] or "")
                    target = label[1] if label else last
                    assert target and stack and stack[-1] in proofs, f"Unmarked proof in {path.name}"
                    assert target not in proof_marks, f"Two main proof marks for {target}"
                    proof_marks[target] = stack[-1]
                else:
                    assert stack and stack[-1] in concepts, f"Unmarked {current} in {path.name}"
                    topic, last = stack[-1], None
            elif fields["label"] and current not in (None, "proof") and last is None:
                last = fields["label"]
                assert last not in statements
                statements[last] = (topic, current)
            elif fields["end"]:
                assert fields["end"] == current
                if current != "proof":
                    assert last, f"Unlabelled {current} in {path.name}"
                    assert stack and stack[-1] == topic, f"Incomplete statement mark at {last}"
                current = topic = None
        assert not stack and current is None, f"Unclosed environment or mark in {path.name}"

    read(PAPER / "main.tex")
    for name, label in named_references:
        assert label in statements and statements[label][1] == name.lower(), (name, label)
    expected = {label for label, (_, kind) in statements.items() if kind != "definition"}
    assert set(proof_marks) == expected, "Numbered results and marked proofs differ"
    assert len({card for card, _ in statements.values()}) == len(statements), "Shared concept destination"
    for label, proof in proof_marks.items():
        concept = statements[label][0]
        assert proofs[proof]["conclusion"] in {s["id"] for s in concepts[concept]["statements"]}, label
    return statements, proof_marks, marks


def check_pdf(paper):
    pdf = ROOT / "paper.pdf"
    assert hashlib.sha256(pdf.read_bytes()).hexdigest() == paper["pdf"]["digest"], "PDF digest mismatch"
    output = subprocess.check_output(["pdfinfo", "-dests", str(pdf)], text=True)
    destinations = {}
    for page, number, which, mode in re.findall(
            r'^\s*(\d+)\s+\[.*?\]\s+"lax\.(\d+)\.([be])\.([hv])"\s*$', output, re.MULTILINE):
        key = (int(number), which)
        assert key not in destinations, f"Duplicate PDF destination {key}"
        destinations[key] = (int(page), mode)
    n = len(paper["marks"])
    assert set(destinations) == {(i, end) for i in range(1, n + 1) for end in "be"}
    for i, mark in enumerate(paper["marks"], 1):
        for which, position in (("b", mark["begin"]), ("e", mark["end"])):
            assert destinations[i, which] == (position["page"], position["mode"]), (i, mark["id"])
    return len(destinations)


def main():
    data = json.loads((ROOT / "build-output.json").read_text())
    assert data["localValidation"]["replay"] is True, "Run lax build . --replay"
    concepts = {c["id"]: c for c in data["concepts"]}
    proofs = {p["id"]: p for p in data["proofs"]}
    statements, proof_marks, source_marks = read_paper(concepts, proofs)
    paper = data["paper"]
    assert source_marks == Counter(mark["id"] for mark in paper["marks"]), "Paper marks differ from source"
    count = check_pdf(paper)
    print(f"{len(proof_marks)} numbered results and {len(statements)-len(proof_marks)} definitions have distinct concept cards.")
    print(f"Every marked proof concludes a statement of its concept.")
    print(f"{len(paper['marks'])} passages and {count} PDF destinations verified across {paper['pdf']['pages']} pages.")


if __name__ == "__main__":
    main()
