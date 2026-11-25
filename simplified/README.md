# A counterexample to Hadwiger's conjecture

This standalone Lax submission (`lax-793645`) gives a proof using quadratic
frames and linear partitions. For arbitrarily large $m$, it constructs a
graph on $m$ vertices with independence number at most 2 in which every
connected matching has fewer than $m/100$ edges. The same graphs disprove
the fractional coloring version of Hadwiger's conjecture.

The [manuscript](paper/main.tex) has 55 pages. Select a numbered statement
in the Lax paper view to open its Lean formulation. Select the proof to see
the results it uses. The last mark opens the graph proof. Each of the 38
numbered results and 2 definitions has its own [concept file](concepts/Lax793645).

To reproduce the archive checks and open the local paper view, run these
commands in this directory.

```sh
lax build . --replay
python3 scripts/check_completion.py --checkpoint
python3 scripts/check_paper_links.py
lax serve .
```

The construction originates in OpenAI's September 2026 preprint. The
[source notice](NOTICE) identifies the original work and the earlier Lean
port. The [dependency audit](references/further-integration-audit.json)
records the results used by the simplified proof.
