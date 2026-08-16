#!/usr/bin/env python3
"""
Comment-aware `sorry`/`admit` counter and build-closure checker for the FLT repo.

The acceptance gate used by the seed-fleet harness compares a global
`sorry`/`admit` count against `baseline + declared_delta`.  A naive
`grep -rE '\\b(sorry|admit)\\b'` cannot tell a proof hole from the word "sorry"
in a docstring: on `daac1f2` it reports 67 where only 56 are live, the other 11
being prose.  That offset is stable only for as long as no packet touches a
prose line, so a *correct* proof that also reflows a stale comment mis-gates.
This script strips `--` line comments and `/- ... -/` blocks (including
docstrings) before matching, and reports the two numbers separately.

It also answers a second gate question that needs no Lean toolchain: which
modules under `FLT/` are outside the default build target's import closure.
`lakefile.toml` declares `globs = ["FLT", "FermatsLastTheorem"]` -- a bare
module name, not `FLT.*` -- so `lake build` compiles exactly what `FLT.lean`
and `FermatsLastTheorem.lean` transitively import.  A packet that adds a new
file without adding its `public import` line to `FLT.lean` gets a green
`lake build` that never compiled the new file.

Usage:
    scripts/sorry_count.py                  # per-file table + totals
    scripts/sorry_count.py --json           # machine-readable, for the gate
    scripts/sorry_count.py --prose          # list the prose occurrences
    scripts/sorry_count.py --closure        # modules outside the build closure
    scripts/sorry_count.py --repo /path/to/FLT

Exit status is 0 unless --closure finds orphan modules (then 1), so it can be
dropped into CI as-is.
"""

import argparse
import json
import os
import re
import subprocess
import sys

TOKEN = re.compile(r"(^|[^A-Za-z_.'])(sorry|admit)([^A-Za-z_']|$)")
IMPORT = re.compile(r"\s*(?:public\s+)?import\s+(FLT[\w.]*)")


def tracked_lean_files(repo):
    out = subprocess.check_output(["git", "-C", repo, "ls-files", "*.lean"], text=True)
    return [f for f in out.split() if not f.startswith("blueprint")]


def split_comments(line, depth):
    """Split one line into (code, prose, new_depth) given the open block depth."""
    code, prose, i = [], [], 0
    while i < len(line):
        if depth > 0:
            close, nest = line.find("-/", i), line.find("/-", i)
            if nest != -1 and (close == -1 or nest < close):
                prose.append(line[i:nest + 2]); i = nest + 2; depth += 1
            elif close != -1:
                prose.append(line[i:close + 2]); i = close + 2; depth -= 1
            else:
                prose.append(line[i:]); i = len(line)
        else:
            block, dash = line.find("/-", i), line.find("--", i)
            if dash != -1 and (block == -1 or dash < block):
                code.append(line[i:dash]); prose.append(line[dash:]); i = len(line)
            elif block != -1:
                code.append(line[i:block]); prose.append("/-"); i = block + 2; depth = 1
            else:
                code.append(line[i:]); i = len(line)
    return "".join(code), "".join(prose), depth


def scan(repo):
    live, prose, prose_lines = {}, {}, []
    for f in tracked_lean_files(repo):
        depth = 0
        with open(os.path.join(repo, f), encoding="utf-8", errors="replace") as fh:
            for n, raw in enumerate(fh, 1):
                line = raw.rstrip("\n")
                code, text, depth = split_comments(line, depth)
                nl, np = len(TOKEN.findall(code)), len(TOKEN.findall(text))
                if nl:
                    live[f] = live.get(f, 0) + nl
                if np:
                    prose[f] = prose.get(f, 0) + np
                    prose_lines.append((f, n, line.strip()))
    return live, prose, prose_lines


def build_closure(repo):
    """Modules reachable from the default build roots, and the orphans under FLT/."""
    files = [f for f in tracked_lean_files(repo) if f.startswith("FLT/")]
    modules = {f[:-5].replace("/", ".") for f in files}
    roots = ["FLT.lean", "FermatsLastTheorem.lean"]

    def imports_of(module):
        path = os.path.join(repo, module.replace(".", "/") + ".lean")
        if not os.path.exists(path):
            return []
        found = []
        with open(path, encoding="utf-8", errors="replace") as fh:
            for line in fh:
                if line.startswith(("theorem", "lemma", "def", "/-!")):
                    break  # imports are confined to the header
                m = IMPORT.match(line)
                if m:
                    found.append(m.group(1))
        return found

    seen, stack = set(), [r[:-5].replace("/", ".") for r in roots]
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        stack.extend(imports_of(mod))
    return sorted(modules - seen)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--repo", default=".", help="repository root (default: cwd)")
    ap.add_argument("--json", action="store_true", help="machine-readable output")
    ap.add_argument("--prose", action="store_true", help="list prose occurrences")
    ap.add_argument("--closure", action="store_true", help="report orphan modules")
    args = ap.parse_args()

    live, prose, prose_lines = scan(args.repo)
    total_live, total_prose = sum(live.values()), sum(prose.values())
    # --json is what the gate calls, so it always carries the closure check.
    orphans = build_closure(args.repo) if (args.closure or args.json) else []

    if args.json:
        json.dump({
            "live": total_live,
            "prose": total_prose,
            "naive": total_live + total_prose,
            "per_file": {f: [live.get(f, 0), prose.get(f, 0)]
                         for f in sorted(set(live) | set(prose))},
            "prose_occurrences": [f"{f}:{n}" for f, n, _ in prose_lines],
            "orphan_modules": orphans,
        }, sys.stdout, indent=2)
        print()
    else:
        for f in sorted(set(live) | set(prose),
                        key=lambda f: (-live.get(f, 0), -prose.get(f, 0), f)):
            print(f"{live.get(f, 0):3d} {prose.get(f, 0):3d}  {f}")
        print(f"\nlive={total_live} prose={total_prose} naive={total_live + total_prose}")
        if args.prose:
            print("\nprose occurrences (do not edit these lines in a proof packet):")
            for f, n, text in prose_lines:
                print(f"  {f}:{n}  {text[:90]}")
        if args.closure:
            print(f"\nmodules under FLT/ outside the `lake build` import closure: "
                  f"{len(orphans)}")
            for o in orphans:
                print("  " + o)

    # Exit status is a CHECK, not a report: only --closure asserts "no orphans".
    # --json always *reports* orphan_modules, but must exit 0 so a caller can
    # distinguish "the tool ran and here are the numbers" from "the tool failed".
    return 1 if (args.closure and orphans) else 0


if __name__ == "__main__":
    sys.exit(main())
