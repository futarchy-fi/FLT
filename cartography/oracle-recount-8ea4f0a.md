# Sorry-oracle recount and hazard report — FLT main @ 8ea4f0a

**Author:** fermat (crew-18), 2026-08-16
**Base verified:** `origin/main` = `8ea4f0a5` (merge of PR #7 / C1, 2026-08-16T11:08:35Z; recount re-run after the merge — unchanged).
Local `main` (454a07b) carries three cartography-only commits on top; the Lean tree is
byte-identical (`git diff --stat origin/main..main -- '*.lean'` is empty), so every count
below is a count against `origin/main`.

## 1. The headline: 71 = 60 + 11

The campaign's generalized oracle rule gates every packet on

> global `sorry`/`admit` count == **71** + declared delta

That constant **71 is not the number of live holes.** Counting with a
comment-and-docstring-aware scanner over `git ls-files '*.lean'` (blueprint excluded):

| | count |
|---|---|
| Live `sorry`/`admit` occurrences (in code) | **60** |
| `sorry`/`admit` occurrences inside line comments, block comments and docstrings | **11** |
| Naive `grep -rE '\b(sorry\|admit)\b'` total | **71** |

60 + 11 = 71 exactly, so the current baseline is internally consistent — but it is
consistent *by accident*, and it is measured by a counter that cannot tell prose from proof.

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

## 4. Live hazard: the packet at the head of the supervisor queue

**hub-oig35.20 (Torsion.lean `WeierstrassCurve.galoisRepresentation`) is exposed.**
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

- new baseline constant: **60** (live), not 71;
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

| Packet | Target | Status vs `8ea4f0a` |
|---|---|---|
| hub-oig35.3 (A14 Pontryagin) | `FLT/Patching/Utils/CompactHausdorffRings.lean:42`, `Group.subsingleton_of_pow_prime_eq_one` | **STILL LIVE** — hole present, statement unchanged. Acceptance under the naive counter is 70; under the corrected counter, 59. Note the file also has one prose occurrence at line 89, so this packet must not touch that docstring. |
| hub-oig35.20 v2 (Torsion DistribMulAction) | `FLT/EllipticCurve/Torsion.lean:109–112` | **STILL LIVE** — all four fields sorried, instance signature unchanged from the refinement analysis in `oig35-20-refinement.md`. Exposed to the §4 hazard. |
| hub-oig35.10 (loc_cst) | — | **STALE, do not requeue** (already recorded: current main proves `loc_cst`; sorry-count acceptance impossible). FLT PR #6 for this packet is still open on GitHub with a green check; it should be closed or rebased, not merged as-is. |

The remaining ready-set packets (hub-oig35.5/.8/.9/.11/.12/.16) cannot be revalidated from
this pod: their target holes are recorded only in beads metadata, and beads is unreachable
from crew-18 (see `outbox/BLOCKERS.md`). The inventory in §2–3 is exactly what a
revalidation needs, so the moment beads returns, each of them is a one-line check against
the table above.
