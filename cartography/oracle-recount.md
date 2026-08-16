# Sorry-oracle recount and hazard report — FLT main

**Author:** fermat (crew-18). Re-run whenever main advances; keep this file at a stable
path and update the revision log rather than renaming it per SHA.

## 0. Revision log

| when (UTC) | main | live | prose | naive | note |
|---|---|---|---|---|---|
| 2026-08-16 11:07 | `148c849` | 60 | 11 | 71 | first comment-aware recount |
| 2026-08-16 11:09 | `8ea4f0a` | 60 | 11 | 71 | after C1 / PR #7 merge — proof-body change only, delta `[0,0]` |
| 2026-08-16 11:58 | `b0fbbec` | **56** | **11** | **67** | after hub-oig35.20 / PR #8 merge — four holes closed, delta `[-4,-4]`, hazard did **not** fire |
| 2026-08-16 12:41 | `daac1f2` | 56 | 11 | 67 | four cartography commits, no `.lean` touched — delta `[0,0]`. Recount re-run from an independently rewritten scanner, now checked in as `scripts/sorry_count.py`. |

**Current baseline: 56 live / 11 prose / 67 naive at `daac1f2`.** Sections 2–3 below are
the inventory as of `8ea4f0a`; the only change since is `FLT/EllipticCurve/Torsion.lean`
9 live → 5 live (its prose count is unchanged at 1).

The counter is no longer a one-off script: `scripts/sorry_count.py` in this repo is the
reference implementation §5 asks for. `--json` emits `live`/`prose`/`naive`, the per-file
table, the prose line list, and the §8 orphan-module check in one call, with no Lean
toolchain required.

## 1. The headline: naive − live = 11, always

The campaign's generalized oracle rule gates every packet on

> global `sorry`/`admit` count == **baseline** + declared delta

and the baseline in use was **71**. That constant **is not the number of live holes.**
Counting with a comment-and-docstring-aware scanner over `git ls-files '*.lean'`
(blueprint excluded), at `8ea4f0a`:

| | count |
|---|---|
| Live `sorry`/`admit` occurrences (in code) | **60** |
| `sorry`/`admit` occurrences inside line comments, block comments and docstrings | **11** |
| Naive `grep -rE '\b(sorry\|admit)\b'` total | **71** |

60 + 11 = 71 exactly, so the baseline was internally consistent — but consistent *by
accident*, and measured by a counter that cannot tell prose from proof. The 11-occurrence
prose offset is the part that matters: it is stable only for as long as no packet touches
a prose line.

## 2. Per-file inventory (live | prose)

| File | live | prose |
|---|---|---|
| `FLT/KnownIn1980s/EllipticCurves/TateCurve.lean` | 11 | 1 |
| `FLT/EllipticCurve/Torsion.lean` | 9 | 1 |
| `FLT/GlobalLanglandsConjectures/GLzero.lean` | 8 | 2 |
| `FLT/Data/HurwitzRatHat.lean` | 4 | 0 |
| `FLT/GaloisRepresentation/HardlyRamified/Frey.lean` | 3 | 0 |
| `FLT/GlobalLanglandsConjectures/GLnDefs.lean` | 3 | 1 |
| `FLT/KnownIn1980s/EllipticCurves/Flat.lean` | 3 | 0 |
| `FLT/Deformations/Representable.lean` | 2 | 0 |
| `FLT/GaloisRepresentation/Automorphic.lean` | 2 | 0 |
| `FLT/KnownIn1980s/PGL2/Defs.lean` | 2 | 0 |
| `FLT/MazurW.lean` | 2 | 0 |
| `FLT/Deformations/LiftFunctor.lean` | 1 | 0 |
| `FLT/GaloisRepresentation/HardlyRamified/Family.lean` | 1 | 0 |
| `FLT/GaloisRepresentation/HardlyRamified/Lift.lean` | 1 | 0 |
| `FLT/GaloisRepresentation/HardlyRamified/ModThree.lean` | 1 | 0 |
| `FLT/GaloisRepresentation/HardlyRamified/Threeadic.lean` | 1 | 0 |
| `FLT/KnownIn1980s/EllipticCurves/GoodReduction.lean` | 1 | 0 |
| `FLT/KnownIn1980s/EllipticCurves/Torsion.lean` | 1 | 0 |
| `FLT/KnownIn1980s/EllipticCurves/WeilPairing.lean` | 1 | 0 |
| `FLT/Patching/Utils/CompactHausdorffRings.lean` | 1 | 1 |
| `FLT/PoitouTate.lean` | 1 | 0 |
| `FLT/Proof.lean` | 1 | 0 |
| `FLT/Assumptions/KnownIn1980s.lean` | 0 | 2 |
| `FLT/Deformations/RepresentationTheory/GaloisRep.lean` | 0 | 1 |
| `FLT/KnownIn1980s/EllipticCurves/ReductionBaseChange.lean` | 0 | 1 |
| `FLT/Slop/DimensionTheorem/Main.lean` | 0 | 1 |
| **total** | **60** | **11** |

## 3. The 11 prose occurrences (the oracle's soft spots)

```
FLT/Assumptions/KnownIn1980s.lean:12                     `knownin1980s` is like `sorry` -- it can be used to prove
FLT/Assumptions/KnownIn1980s.lean:41                     of FLT which is sorry-free but which uses `knownin1980s` liberally.
FLT/Deformations/RepresentationTheory/GaloisRep.lean:385 …state the aforementioned result as a sorry.
FLT/EllipticCurve/Torsion.lean:114                       -- the next `sorry` is data but the only thing which should be missing is
FLT/GlobalLanglandsConjectures/GLnDefs.lean:333          --   sorry
FLT/GlobalLanglandsConjectures/GLzero.lean:76            --   sorry
FLT/GlobalLanglandsConjectures/GLzero.lean:137           -- is_finite_cod := sorry -- needs a better name
FLT/KnownIn1980s/EllipticCurves/ReductionBaseChange.lean:217  (An honest definition, not a sorry: it is
FLT/KnownIn1980s/EllipticCurves/TateCurve.lean:500       -- `weilPairing` and `tateEquiv`/`tateEquivSepClosure` are all currently `sorry`ed data,
FLT/Patching/Utils/CompactHausdorffRings.lean:89         /-- A connected compact Hausdorff abelian topological group…
FLT/Slop/DimensionTheorem/Main.lean:46                   is `sorry`-free.
```

## 4. The hazard, and what happened when it was tested

> **OUTCOME, 2026-08-16T11:40Z — the hazard did NOT fire.** hub-oig35.20 shipped as FLT
> PR #8 and merged as `b0fbbec`. The worker's diff is confined to the instance block
> (lines 106–112 → the four `by` proofs), the line-109 trailing comment goes with the line
> it annotated, and the line-114 prose remark is untouched. Post-merge counts are exactly
> 56 live / 11 prose / **67 naive** = 71 − 4, so the declared `[-4,-4]` budget passed under
> both the naive and the corrected counter. **What saved it was the packet's edit-region
> restriction** ("instance block only", from `oig35-20-refinement.md` §4) — not the gate,
> which would have accepted a −5 as readily as it would have rejected it. The analysis
> below therefore stands as a live risk for every packet that does *not* carry an
> edit-region restriction, which is most of them.

**hub-oig35.20 (Torsion.lean `WeierstrassCurve.galoisRepresentation`) was exposed.**
Its four target holes are `FLT/EllipticCurve/Torsion.lean:109–112`
(`one_smul`, `mul_smul`, `smul_zero`, `smul_add`). Two lines below them sits

```
109:      one_smul := sorry -- these should all be easy
...
112:      smul_add := sorry
113:
114: -- the next `sorry` is data but the only thing which should be missing is
```

A worker that proves the instance and — entirely reasonably — also deletes or rewords the
now-stale line-109 trailing comment or the line-114 remark will move the naive count by
**−5 or −6, not −4**. The packet declares delta `[-4,-4]`; the gate then rejects a correct
proof. This is not hypothetical: line 109's comment ("these should all be easy") is exactly
the kind of line a worker deletes on success.

The same trap exists for any packet on `GLzero.lean` `ofComplex` (live holes at 134, 135,
136, 138; prose at 137, and 137 is a *commented-out field of the same structure*), and for
`TateCurve.lean` (11 live, prose at 500 summarising which of them are sorried).

## 5. Recommended fix (cheap, no packet re-authoring)

Replace the naive counter in the acceptance gate with a comment-stripped counter, and pin
the baseline to the live number:

- new baseline constant: the **live** count, not the naive one — **56 at `daac1f2`**
  (it was 60 when this section was written, at `8ea4f0a`; read it off §0, never from here);
- counter: strip `--` line comments and `/- … -/` block comments/docstrings before matching
  `(^|[^A-Za-z_.])(sorry|admit)([^A-Za-z_]|$)`;
- keep the existing per-packet delta budgets unchanged — they are deltas, so they carry over
  verbatim;
- add a second, advisory check `prose_count == 11` so that a packet which *does* touch a
  prose line is flagged rather than silently mis-gated.

If changing the counter is judged too invasive mid-wave, the minimum safe patch is to add to
every packet's `write_paths` contract the clause **"do not modify any line matching
`sorry`/`admit` that is not the declared target"**, and to record 71 = 60 live + 11 prose in
the packet metadata so a failing gate can be triaged in one step instead of a re-run.

A reference implementation of the comment-aware counter is the scanner used for this
document; it is ~20 lines of Python and needs no Lean toolchain, so it can run in the
acceptance harness before `lake build`.

## 6. Revalidation of the ready-set targets that are reachable from the repo

| Packet | Target | Status vs `b0fbbec` |
|---|---|---|
| hub-oig35.3 (A14 Pontryagin) | `FLT/Patching/Utils/CompactHausdorffRings.lean:42`, `Group.subsingleton_of_pow_prime_eq_one` | **STILL LIVE** — hole present, statement unchanged. Acceptance is now **66 naive / 55 live** (baseline 67/56 with delta `[-1,-1]`) — the constant moved when PR #8 merged, so a packet still carrying `70` will false-fail. Note the file also has one prose occurrence at line 89, so this packet must not touch that docstring. |
| hub-oig35.20 v2 (Torsion DistribMulAction) | `FLT/EllipticCurve/Torsion.lean:109–112` | **DONE — merged as `b0fbbec`** (PR #8, 2026-08-16T11:40:11Z). The v2 primary route from `oig35-20-refinement.md` §4 was used verbatim: `cases P <;> rfl` for `one_smul`/`mul_smul`, `rfl` for `smul_zero`, `map_add (…Point.map _) P Q` for `smul_add`. Delta `[-4,-4]` honoured. |
| hub-oig35.10 (loc_cst) | — | **STALE, do not requeue** (already recorded: current main proves `loc_cst`; sorry-count acceptance impossible). FLT PR #6 for this packet is still open on GitHub with a green check; it should be closed or rebased, not merged as-is. |

The remaining ready-set packets (hub-oig35.5/.8/.9/.11/.12/.16) cannot be revalidated from
this pod: their target holes are recorded only in beads metadata, and beads is unreachable
from crew-18 (see `outbox/BLOCKERS.md`). The inventory in §2–3 is exactly what a
revalidation needs, so the moment beads returns, each of them is a one-line check against
the table above.

## 7. Two systemic observations from the PR #8 merge (worth fixing before the wave)

**(a) Fleet branches are cut from a stale base.** PR #8's merge base is `3035736`, two
commits behind main at the time it opened. It was harmless here — `FLT/EllipticCurve/Torsion.lean`
is byte-identical at `3035736`, `148c849` and `8ea4f0a` (blob `0e3b90e5`), so the proof
applied cleanly and the three-dot diff is one file, +12/−4. But the *two-dot* diff
`origin/main..pr8` shows the C1 witness curve reverted (`⟨0,0,0,-4,0⟩ → ⟨0,0,0,-1,0⟩`) and
`cartography/oig35-20-refinement.md` deleted, because those changes simply do not exist on
the branch. Merge semantics discarded both, and the merged tree is correct — verified by
`git merge-tree` before the merge and by recount after it.

The next packet whose target file *has* changed since its base will not be so lucky: the
acceptance gate runs `lake build` and a count on the branch, both of which pass against the
stale tree, and the merge then silently drops or resurrects whatever moved in between.
**Fix: rebase each fleet branch onto current main before opening the PR, or make the gate
compute its count against the merge result rather than the branch tip.**

**(b) "Green" on a fleet PR is currently a receipt, not a build.** PR #8's only status is
`Seed Fleet / independent review — Independent review … validated`; `check-runs` is empty.
There is no `lake build` signal on the commit for a reviewer to read. The review receipt
may well be backed by a build inside the harness, but nothing on the PR says so, and a
human merging on a green tick is not seeing compile evidence. **Fix: publish the build
result as a check-run (name, conclusion, and the observed sorry count) alongside the review
receipt.** This is also what would let an orchestrator without a Lean toolchain — such as
crew-18 — distinguish "reviewed" from "compiles".

## 8. Build-closure hazard — `lake build` does not compile every file the oracle counts

**Found 2026-08-16T12:41Z at `daac1f2`. This is a second, independent way for the gate to
read green on work it never checked, and unlike §4 it is firing today.**

`lakefile.toml` declares the default target as

```toml
defaultTargets = ["FLT"]
[[lean_lib]]
name = "FLT"
globs = ["FLT", "FermatsLastTheorem"]
```

`"FLT"` is a **bare module name, not a glob over the directory** — contrast the test
library two stanzas down, which correctly writes `globs = ["FLTTest.*"]`. So `lake build`
compiles exactly the transitive import closure of `FLT.lean` and `FermatsLastTheorem.lean`,
and `FLT.lean` is a hand-maintained list of 260 `public import` lines. The sorry-oracle, by
contrast, counts over `git ls-files '*.lean'` — every tracked file, closure or not. The two
sets are not equal.

**Two files under `FLT/` are outside the closure right now:**

```
FLT.MazurW        (FLT/MazurW.lean)     — 2 live sorries, counted by the oracle
FLT.PoitouTate    (FLT/PoitouTate.lean) — 1 live sorry,  counted by the oracle
```

Neither module name appears in any `import` line anywhere in the repository —
`FLT.lean`, the other 260 `FLT/` files, `FLTTest`, and `FermatsLastTheorem.lean` all
omit them. Reproduce with `scripts/sorry_count.py --closure` (exit 1 when orphans exist),
or with `grep -rn 'import FLT.MazurW' --include='*.lean' .` for the one-liner.

**Why this matters to the campaign specifically.** `FLT/MazurW.lean` is the C1 calibration
file. Four merged packets have targeted it — hub-bv6v2.1 (statement scaffold, 4 sorries by
design), hub-oig35.1 and hub-oig35.2 (the two `mazur_W` witness proofs), and hub-oig35.18 /
PR #7 (the C1 leg, which changed the `mazur_W_nonvacuity_full_two_torsion` witness curve).
On the reading above, the `lake build` in each of those acceptance runs **did not compile
the file being changed**. Their three sorries still move the oracle count, so the count
gate was live for them; only the compile gate was vacuous. C1 was the leg of harness
selection `hub-r7qdn.7` that was supposed to prove the harness can produce *compiling*
proofs, so this bears directly on whether C1 should be counted as calibration evidence.

**Stated limits of this finding.** crew-18 has no Lean toolchain, so this is a reading of
`lakefile.toml` plus a complete grep of the import graph, not an observed build. Two things
would falsify it and both are one command for anyone holding the toolchain:

1. the harness may invoke explicit module targets (`lake build FLT.MazurW`) rather than the
   default target — check the acceptance runner's actual command line;
2. Lake's bare-name glob semantics may differ from the reading above — check with
   `lake build --no-build -v 2>&1 | grep -c MazurW`, or simply introduce a syntax error
   into `FLT/MazurW.lean` and confirm `lake build` still exits 0.

If either falsifies it, delete this section. If neither does, it is a gate hole.

**Fixes, cheapest first.**

- **Now, per packet:** every packet whose `write_paths` include a `.lean` file must declare
  the module that puts it in the closure, and the gate must confirm the target file is
  reachable from `FLT.lean`. For a packet that *creates* a file this means the diff must
  also add the alphabetized `public import` line to `FLT.lean` — otherwise the new file is
  never compiled and the packet passes on an empty build. Every wave-3 envelope carries
  this as gate clause 8.
- **Now, one line, repo-wide:** add `public import FLT.MazurW` and `public import
  FLT.PoitouTate` to `FLT.lean` and let the build tell us whether those three files
  actually compile. Expect this to surface real errors — nothing has type-checked them
  since they were written, and `FLT/MazurW.lean` last changed under a provider fixture
  patch (`cf19681`). Do it as its own packet, delta `[0,0]`, so a failure is attributable.
- **Structural:** change the glob to `["FLT.*", "FLT", "FermatsLastTheorem"]` so the library
  is the directory, and orphaning becomes impossible rather than merely detectable. This is
  the upstream-correct fix but it is a repo-policy change; the FLT maintainers may have
  chosen the curated root deliberately, so propose, do not merge unilaterally.
- **In CI:** run `scripts/sorry_count.py --closure` alongside the count. It exits 1 on any
  orphan and needs no toolchain, so it costs nothing.
