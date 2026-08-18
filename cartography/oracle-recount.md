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

### 8b. The hazard fired again — on the C2 calibration packet itself (2026-08-16T15:24Z)

§8 predicted that any packet creating a new file without an `FLT.lean` import line would get
a green build that never compiled it. **PR #9 — hub-oig35.19, the C2 calibration leg, merged
as `754e092` and declared GREEN — did exactly that.**

It added `FLT/NumberField/ZetaFE/ZeroTheoryN2.lean`: 140 lines, two lemmas, zero sorries,
node N2 of `odlyzko-m3-decomposition.md`. Verified against `754e092`:

- **Orphan.** The string `ZeroTheoryN2` occurs nowhere in the repository except inside the
  file itself (its own `namespace` open and close). `FLT.lean` does not import it; no `FLT`
  module does. `scripts/sorry_count.py --closure` now lists three orphans, up from two.
- **Not in the module idiom.** 261 of the 263 files under `FLT/` begin with `module`. This
  one does not, and has no `public import` lines and no `@[expose] public section` — it uses
  plain `import`. The other two non-conforming files are, fittingly, the two pre-existing
  orphans.
- **Invisible to the axiom census**, since `FermatsLastTheorem.lean` reaches it through
  nothing.

The count gate could not have caught this: the file adds no sorries, so `67 → 67` is correct
and the packet passed honestly on the number it was given.

**Consequence for `hub-r7qdn.7`.** Both calibration legs now have the same shape: C1 edited
an orphan (`FLT/MazurW.lean`), C2 created one. If the acceptance runner builds the default
target, neither leg compiled the file it was judged on, and the harness-selection evidence
is weaker than it looks on the day it closes.

**In fairness, one step could exonerate C2.** The isolated `flt-acceptance` runner may build
by explicit module target rather than via the default target, in which case the file *was*
compiled and this is a project-wiring defect rather than a vacuous verdict. That is a
one-command check — read what `flt-acceptance` actually invokes — and it should be done
before anyone either closes `hub-r7qdn.7` or reopens it. Packet `C2-CLOSURE-FIX` carries
both the repair and that fairness note.

### 8c. SETTLED EMPIRICALLY — W3-00 was run on 2026-08-17T23:15Z, and §8 is confirmed

Everything above about the build-closure hazard was a *textual* argument: I read
`lakefile.toml`, read Lake's glob semantics, and inferred that orphan modules are never
compiled. Kelvin granted crew-18 toolchain access today (`lean` 4.34.0-rc1, commit
`3447a668783dbce1a8fdb97101dd067687b2b418`; `lake` 5.0.0-src+3447a66, both fixed under
`/usr/local/bin`, no `elan`), so the inference is now an experiment.

**W3-00 does not need Mathlib.** The whole question is Lake glob semantics, so it can be
settled in a throwaway package with FLT's exact glob shape and no dependencies — seconds,
not the hours a warm FLT build would cost. The package: a root `Root.lean` importing
`Root.Imported`, plus `Root/Orphan.lean` containing a deliberate hard type error.

**Run 1 — `globs = ["Root"]`, which is FLT's shape (`globs = ["FLT", "FermatsLastTheorem"]`):**

```
✔ [2/4] Built Root.Imported (6.5s)
✔ [3/4] Built Root (445ms)
Build completed successfully (4 jobs).
EXIT=0
```

`Root/Orphan.lean` was never compiled. **`lake build` reports success, exit 0, over a file
containing a type error.** That is the hazard, reproduced exactly.

**Run 2 — same tree, `globs = ["Root.+"]`:**

```
✔ [2/4] Built Root.Imported (829ms)
✖ [3/4] Building Root.Orphan (842ms)
error: Root/Orphan.lean:1:20: Type mismatch
  "this is a type error and will not compile" has type String but is expected to have type Nat
error: build failed
EXIT=1
```

So the bare-module glob is precisely the cause, and the recursive glob is precisely the
cure. **A bare `"FLT"` glob means the single module `FLT`; the default target is therefore
the import closure of the hand-maintained `FLT.lean`, and nothing else.**

**Confirmed against live main at `e2c90e1`:** `FLT.lean` imports none of
`FLT.MazurW`, `FLT.PoitouTate`, `FLT.NumberField.ZetaFE.ZeroTheoryN2`, and a repo-wide grep
finds **no file anywhere** importing them. `scripts/sorry_count.py --closure` reports the
same three and **exits 1** (verified; the plain invocation exits 0). The gate I have been
recommending works as specified.

**The fix is NOT simply changing the glob to `"FLT.+"`, and this is the part to get right.**
The three orphans hold real defects — `ZeroTheoryN2.lean` alone produced 124 `Ambiguous
term` / 126 `unsolved goals` / 137 `type mismatch` errors on its first real compilation
(§8b). Flipping the glob today converts a silently-passing repo into a **repo-wide red
build**, which is worse than the hazard for anyone who has to merge in the meantime. And
stubbing the orphans with `sorry` to make them compile moves naive 67 → 69 and false-fails
every packet gated on the constant. Ordering that works:

1. **Wire `scripts/sorry_count.py --closure` into `flt-acceptance` now.** It needs no
   toolchain, exits 1 on orphans, and turns the hazard from silent into loud without
   touching the build.
2. **Repair the three orphans** (`oig35-21-refinement.md` has the per-line work for
   `ZeroTheoryN2`), each on its own branch.
3. **Only then flip `globs` to `["FLT.+", "FermatsLastTheorem"]`**, in one atomic commit
   with the last repair, and re-pin every packet constant in the same change.

Step 1 is a one-line CI addition and closes the vacuous-green class permanently. It should
not wait on steps 2 and 3.

---

## 9. Two acceptance conventions live in this campaign, and confusing them costs a retraction

Added 2026-08-17T23:44Z, after I published a wrong gate audit and had to retract it on six
beads. **The seed-fleet packets and the cartography packets do not gate the same way, and a
constant that is "stale" in one convention is correct in the other.**

### 9a. Seed-fleet convention — anchored pre/post pair

Decoded from `metadata.packet_refinement_receipt_uri` (a `data:application/json;base64,` blob
on every `hub-oig35.*` bead; base64-decode it to read `contract.acceptance_commands`). The
gate is:

```
/usr/local/bin/flt-acceptance range <BASE_REVISION> <PRE> <POST_MIN> <POST_MAX>
```

`PRE` is the naive count **at `BASE_REVISION`**, not at HEAD. Measured live against
`origin/main` at `e1f5d21`:

| bead | acceptance base | naive @ that base | PRE | post range | target holes | check |
|---|---|---|---|---|---|---|
| hub-oig35.5 | `e99f1674` | 71 | 71 | 0–72 | 1 | consistent (loose) |
| hub-oig35.8 | `30357369` | 71 | 71 | 69–69 | 2 | 71−2 = 69 ✔ |
| hub-oig35.9 | `e99f1674` | 71 | 71 | 0–70 | 1 | consistent (loose) |
| hub-oig35.11 | `e99f1674` | 71 | 71 | 0–70 | 1 | consistent (loose) |
| hub-oig35.12 | `30357369` | 71 | 71 | 69–69 | 2 | 71−2 = 69 ✔ |
| hub-oig35.16 | `30357369` | 71 | 71 | 68–68 | 3 | 71−3 = 68 ✔ |
| hub-oig35.19 | `e99f1674` | 71 | 71 | 67–67 | 0 (new file) | passed only by drift — see 9c |

**Every one of these is correct at its own base.** Today's baseline (naive 67) is irrelevant
to them. Judging them against 67 is what produced the retracted audit.

### 9b. Cartography convention — absolute against HEAD

The wave-2/wave-3 envelopes in this repo pin a single number read off §0 of this file and
gated with `grep -qx <N>` against the working tree. They carry **no base revision**, so the
constant genuinely does go stale on every merge — which is why §7 and the wave-3 preamble
warn that a packet still carrying `71` will false-fail. **That warning is about *our* packets
and does not transfer to the seed-fleet ones.**

**If you write a packet, say which convention you are in, in the packet.** The one-word fix
for the cartography family is to adopt 9a's shape: carry the base revision beside the
constant, so the pair can be checked instead of trusted.

### 9c. The defect that a delta framing would actually fix

`hub-oig35.19` names **three** baselines: `metadata.base_revision = 8408ec31` (naive 67), the
acceptance command `range e99f1674 71 67 67` (`e99f1674` is naive 71), and its own context
prose, *"The baseline includes merged PRs #7/#8 and has 67 sorry/admit occurrences."* It
passed only because the drift between the two bases (71 → 67) happened to equal the delta the
range demanded (0). `hub-oig35.5` has the same shape — prose says "the current 72-occurrence
baseline" (correct for its `base_revision` 6ce191d4, naive 72), while the command passes
`PRE=71` (correct for `e99f1674`). Two revisions, one packet, and no check that they agree.

### 9d. Three packets are based off `main`

`hub-oig35.5` pins `base_revision = 6ce191d4` (naive 72); `.9` and `.11` pin `cb0b7c18`
(naive 71). **Neither commit is an ancestor of `main`** — both are on
`fleet/hub-oig35-10-c9a01f5706fdc3cc9984-r1`, the branch behind **PR #6**, open since
2026-08-14. `.9` and `.16` are the only two packets currently in `packet_ready`, so closing
PR #6 orphans the base of the work that is actually dispatchable. Decide PR #6 and re-base
these three in the same motion.

### 9e. Two mechanical traps in reading the bead DB — both produced wrong counts tonight

**`bd list` truncates silently.** It defaults to `--limit 50` *and* to open statuses. Quoting a
count off a bare `bd list` gave me a 10-bead sample of what is really a 21-bead set, in a DB
that holds 1482 beads. Always:

```
bd list --status open,in_progress,blocked,deferred,closed --limit 0 --json
```

`bd show` reaches beads that a truncated `bd list` omits, which is how two disjoint views of
the same set can appear within one hour.

**`metadata.state` is not cleared on close.** `hub-oig35.6`, `.7` and `.17` are all
`status=closed` while still carrying `state=packet_ready`. State must be read together with
status or finished work counts as queued work.

**Corrected census of `hub-oig35.*`, 2026-08-18T00:12Z — 21 beads, 16 open, 5 closed:**

| state (open only) | count | beads |
|---|---|---|
| `packet_ready` | 3 | .4, .9, .16 |
| `needs_refinement` | 7 | .8, .10, .12, .18, .19, .20, .21 |
| `manual_review_required` | 2 | .5, .11 |
| `curated_not_ready` | 1 | .3 |
| *(no state field)* | 3 | .13, .14, .15 — created by `fleet-autocommit`, metadata holds only `refinement` |

Between 3 and 6 pickable packets against 20 pods, with 7 parked behind a refinement pass that
is not running. Any earlier "2 of 10" figure of mine is withdrawn.

---

## 10. §8 settled by compilation, not by reading — and one of its claims retracted

**2026-08-18T00:13Z. crew-18 now has a working Lean toolchain**, so the two falsifiers §8
listed for itself are both closed, on the real tree rather than on a throwaway package.
Method: `git clone` of `main` into `/tmp/fltbuild` (deliberately **not** the working tree —
writing `.lake` into `FLT/` is the oracle defect named in `hub-oig35.19`'s own context),
`lake exe cache get` (8691 files, mathlib `bc06ce9f87cd`), then `lake env lean <file>` per
orphan. `lake env lean` compiles one module against the package's own environment, which is
exactly the "would this file build if the closure included it" question.

### 10a. The three orphans, compiled

| module | exit | errors | live sorries | note |
|---|---|---|---|---|
| `FLT.MazurW` | **0** | 0 | 2 — `14:8`, `24:8` | linter warnings only (`haveI`/`simpa` style) |
| `FLT.PoitouTate` | **0** | 0 | 1 — `51:8` | `greenbergWilesOrderFormula` |
| `FLT.NumberField.ZetaFE.ZeroTheoryN2` | **1** | **1** | 0 | fails at line 1, import resolution |

The MazurW sorries are `mazur_W` and `mazur_W_ge11` — **the file's two headline theorems,
still unproved**, in the C1 calibration file. PoitouTate's is the Greenberg–Wiles order
formula. All three are counted by the oracle and none of them is compiled by `lake build`.

### 10b. ZeroTheoryN2 has never compiled, anywhere

```
FLT/NumberField/ZetaFE/ZeroTheoryN2.lean:1:0: error: object file
'.../Mathlib/Analysis/SpecialFunctions/Trigonometric/Identities.olean'
of module Mathlib.Analysis.SpecialFunctions.Trigonometric.Identities does not exist
```

`Mathlib.Analysis.SpecialFunctions.Trigonometric.Identities` **does not exist at the pinned
mathlib revision** — the directory holds `Angle`, `Arctan`, `Basic`, `Bounds`, `Complex`,
`Cotangent`, `Deriv`, `EulerSineProd`, `Inverse`, `Meromorphic`, `Series`, `Sinc`, and no
`Identities`. The file's other four imports all resolve. This is C2 — `hub-oig35.19`, merged
as PR #9 at 2026-08-16T15:09Z. It passed acceptance because it is an orphan (so the compile
gate never saw it) and because its count gate only grepped for `sorry`, of which it has none.

**A file that cannot parse its own imports was merged into `main` as calibration evidence
that the harness produces compiling proofs.** That is the §8 hazard firing at full strength
on the one packet whose entire purpose was to measure whether the harness works.

### 10c. Retraction — "flipping the glob turns silent-green into repo-wide red"

`BLOCKERS.md` said not to flip `globs` because the orphans "hold real defects
(`ZeroTheoryN2` produced 124/126/137 errors on first compilation)". **Measured, that is
false.** Two of the three orphans compile green today. The third stops at import resolution,
so nothing downstream of line 1 has ever been elaborated and its error count is *unknown* —
124/126/137 was a figure I inherited from a packet's prose and repeated as if it were an
observation. It was not one.

**The corrected cost of closing this hazard is the repair of exactly one file.** The staged
order in `BLOCKERS.md` stands, but it is much cheaper than advertised:

1. wire `scripts/sorry_count.py --closure` into `flt-acceptance` — one CI line, no toolchain;
2. repair `ZeroTheoryN2` (import fix, then whatever it exposes);
3. flip `globs` to `["FLT.+", "FermatsLastTheorem"]` atomically with step 2.

Note that step 3 changes no counts: the three orphans' 3 live sorries are already inside the
oracle's 56, because the oracle scans `git ls-files`, not the build closure. Flipping the
glob makes the compiler agree with the counter; it does not move the number.

### 10d. What is behind line 1: the first real measurement, and it is not a typo

Substituting the one bad import for `Mathlib.Analysis.Complex.Trigonometric` (which does
supply `Complex.sin_add_pi` and `Complex.sin_mul_I`, the two lemmas the file actually cites)
lets the file elaborate. It then produces **15 errors in 140 lines**:

| line | error |
|---|---|
| 27:38 | ambiguous term `sinh` — `Real.sinh` vs `Complex.sinh` both in scope |
| 42:26 | `rewrite` failed: no occurrence of `Complex.sin (?x + ↑π)` — the goal is `sin (↑π + ↑π * (I * ↑t))`, argument order reversed |
| 47:67 | type mismatch on `sin_mul_I` — mathlib states `sin (x * I) = sinh x * I`, the file wants `sin (π * I * t) = I * sinh (π * t)` |
| 52:13 | application type mismatch |
| 53:59 | type mismatch |
| 65:8 | `rewrite` failed |
| 78:4, 80:4, 83:4 | type mismatch after simplification |
| 88:92 | unsolved goals |
| 99:8 | `rewrite` failed |
| 118:44, 122:49 | ambiguous term |
| 124:43 | unsolved goals |
| 135:4 | type mismatch after simplification |

**These are not import errors.** Reversed argument orders, a lemma statement remembered
wrongly, unsolved goals, ambiguity from an open namespace — the proof body was written
against a Mathlib API it was never checked against. A different import substitution would
shift the details; it would not touch these three classes.

**So the honest calibration result for C2 is: the packet delivered no working proof.** It is
`sorry`-free, so the count gate read it as clean; it is an orphan, so the compile gate never
ran; compiled, essentially every step fails. This is the exact failure mode §4 and §8 were
written to predict, observed end-to-end on a merged commit for the first time.

Caveat stated plainly: 15 is the count under *my* import substitution. Whoever repairs the
file should re-measure after choosing the import properly. What does not depend on that
choice is that the body does not compile.
