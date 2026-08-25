# Benchmark harness

`bench.py` times `cn verify` against `soteria-cn verify` over the test
corpus (`test/*.t/*.c`), keeping only files that **both** tools fully verify
(so designed-negative tests and one-tool-only files are excluded), and
prints a markdown table with per-file speedups and the geometric mean.

```sh
python3 bench/bench.py [--runs N] [--timeout SECS]
```

It needs the `soteria-install` opam switch (for `cn` and the cerberus
runtime), Z3 on the configured path, and a built workspace
(`dune build soteria-cn/bin`); the `soteria-cn` binary is taken from
`_build/`.

## Notes on a first run (2026-08-25, 3 runs)

- 23-file corpus, geometric mean speedup **1.5x**. All files are small, so
  wall time is dominated by process startup for both tools (~60–300 ms);
  this measures overhead, not solver scaling.
- `cn` **times out** (120 s) on `verif.t/lists.c` and `verif.t/dll.c`,
  which soteria-cn verifies in under a second. These files were written with
  soteria-cn's unfold heuristics in mind and lack the manual
  unfold/lemma annotations CN would need — a documented one-directional
  delta, and the first data point suggesting the interesting performance
  comparisons need annotation-matched, larger programs.
- Several other `cn: 1` skips are the same delta (CN needs annotations the
  file does not carry) or designed-negative tests.
