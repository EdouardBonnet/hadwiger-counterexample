#!/usr/bin/env python3
"""Index the pinned paper's shared theorem counter, including remarks.

This is specific to this paper's one-section-per-input layout. It does not
attempt to implement TeX. Labels identify the declaration itself, not a
subsequent labelled equation inside an otherwise unlabelled declaration.
"""

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "references/openai/paper-source"


def main():
    main_tex = (SOURCE / "main.tex").read_text()
    preamble = (SOURCE / "preamble.tex").read_text()
    environments = re.findall(r"\\newtheorem\{([^}]+)\}", preamble)
    header = re.compile(
        r"\\begin\{(" + "|".join(map(re.escape, environments)) + r")\}"
        r"(?:\[([^\]]*)\])?(?:\s*\\label\{([^}]+)\})?"
    )
    result = []
    for section, include in enumerate(
        re.finditer(r"\\input\{(sections/[^}]+)\}", main_tex), start=1
    ):
        path = SOURCE / (include[1] + ".tex")
        body = path.read_text()
        if len(re.findall(r"\\section\{", body)) != 1:
            raise ValueError(f"Review section numbering for {path}")
        for number, match in enumerate(header.finditer(body), start=1):
            result.append({
                "section": section,
                "number": f"{section}.{number}",
                "kind": match[1],
                "title": match[2],
                "label": match[3],
                "source": str(path.relative_to(ROOT)),
                "line": body.count("\n", 0, match.start()) + 1,
            })
    (ROOT / "references/paper-statements.json").write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + "\n"
    )
    print(f"Indexed {len(result)} numbered declarations, including remarks.")


if __name__ == "__main__":
    main()
