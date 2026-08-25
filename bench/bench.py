#!/usr/bin/env python3
"""Benchmark `cn verify` against `soteria-cn verify` over the test corpus.

Discovers every `.c` file under `test/*.t/`, keeps those that BOTH tools
fully verify (exit code 0), then times each tool over `--runs` runs and
prints a markdown table with per-file speedups and the geometric mean.

Requires the `soteria-install` opam switch (both binaries) and Z3. Run from
anywhere:

    python3 bench/bench.py [--runs N] [--timeout SECS]
"""

import argparse
import glob
import math
import os
import statistics
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SWITCH = "soteria-install"
Z3_DIR = "/local/scratch/nk480/smt-solvers/install/bin"


def opam_env():
    out = subprocess.run(
        ["opam", "env", f"--switch={SWITCH}", "--set-switch", "--shell=sh"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    env = dict(os.environ)
    for line in out.splitlines():
        # lines look like: VAR='value'; export VAR;
        if "=" not in line:
            continue
        var, _, rest = line.partition("=")
        value = rest.split("; export")[0].strip().strip("'")
        env[var] = value
    env["PATH"] = Z3_DIR + os.pathsep + env.get("PATH", "")
    return env


def find_tools(env):
    def which(name):
        for d in env["PATH"].split(os.pathsep):
            p = os.path.join(d, name)
            if os.path.isfile(p) and os.access(p, os.X_OK):
                return p
        sys.exit(f"error: {name} not found on the switch PATH")

    # soteria-cn is typically not installed; use the workspace build.
    built = os.path.join(
        os.path.dirname(ROOT), "_build", "default", "soteria-cn", "bin", "main.exe"
    )
    scn = built if os.path.isfile(built) else which("soteria-cn")
    return which("cn"), scn


def run_once(cmd, cwd, env, timeout):
    start = time.perf_counter()
    try:
        proc = subprocess.run(
            cmd,
            cwd=cwd,
            env=env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            timeout=timeout,
        )
        return time.perf_counter() - start, proc.returncode
    except subprocess.TimeoutExpired:
        return timeout, None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", type=int, default=5)
    ap.add_argument("--timeout", type=float, default=120.0)
    args = ap.parse_args()

    env = opam_env()
    cn, scn = find_tools(env)

    files = sorted(glob.glob(os.path.join(ROOT, "test", "*.t", "*.c")))
    corpus = []
    for f in files:
        cwd = os.path.dirname(f)
        base = os.path.basename(f)
        _, rc_cn = run_once([cn, "verify", base], cwd, env, args.timeout)
        _, rc_scn = run_once([scn, "verify", base], cwd, env, args.timeout)
        if rc_cn == 0 and rc_scn == 0:
            corpus.append(f)
        else:
            rel = os.path.relpath(f, ROOT)
            print(
                f"skipping {rel} (cn: {rc_cn}, soteria-cn: {rc_scn})",
                file=sys.stderr,
            )

    print(f"corpus: {len(corpus)} files, {args.runs} runs each\n", file=sys.stderr)

    rows = []
    for f in corpus:
        cwd = os.path.dirname(f)
        base = os.path.basename(f)
        times = {}
        for name, tool in (("cn", cn), ("soteria-cn", scn)):
            samples = []
            for _ in range(args.runs):
                t, rc = run_once([tool, "verify", base], cwd, env, args.timeout)
                if rc != 0:
                    sys.exit(f"error: {name} failed on {base} during timing")
                samples.append(t)
            times[name] = samples
        rows.append((os.path.relpath(f, os.path.join(ROOT, "test")), times))

    def fmt(samples):
        m = statistics.mean(samples)
        sd = statistics.stdev(samples) if len(samples) > 1 else 0.0
        return f"{m:.3f} ± {sd:.3f}"

    print("| file | cn (s) | soteria-cn (s) | speedup |")
    print("|---|---:|---:|---:|")
    speedups = []
    for rel, times in rows:
        m_cn = statistics.mean(times["cn"])
        m_scn = statistics.mean(times["soteria-cn"])
        speedup = m_cn / m_scn if m_scn > 0 else float("inf")
        speedups.append(speedup)
        print(
            f"| {rel} | {fmt(times['cn'])} | {fmt(times['soteria-cn'])} "
            f"| {speedup:.1f}x |"
        )
    if speedups:
        geo = math.exp(sum(map(math.log, speedups)) / len(speedups))
        print(f"\ngeometric mean speedup: **{geo:.1f}x**")


if __name__ == "__main__":
    main()
