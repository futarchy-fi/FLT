# R5c result

Completed on `task/r5c`, without pushing. Checked at 2026-09-28 01:15:42 UTC.

- `3303dbc8`: `DiscreteValuationRing/Monogenic.lean` proves that a finite
  intermediate algebra surjecting onto the residue field and containing a
  uniformizer is the full DVR.
- `2ee532bb`: `DiscreteValuationRing/ResidueGenerator.lean` constructs a
  generator by adjusting a simple residue root by a uniformizer. It proves
  monogenicity and power-basis existence for a finite free DVR algebra with
  separable residue extension.
- `3d46392b`: `GroupScheme/LocalIntegralPowerBasis.lean` constructs
  `ThreeAdicPlan.threeAdicIntegersPowerBasis L` for every finite extension
  `L/ℚ_[3]` and proves
  `ThreeAdicPlan.threeAdicDifferent_eq_annihilator_kaehlerDifferential`.
  Neither conclusion assumes a power basis or differential annihilation.

Reproduce the successful targeted builds, one at a time:

```sh
lake build FLT.Mathlib.RingTheory.DiscreteValuationRing.Monogenic
lake build FLT.Mathlib.RingTheory.DiscreteValuationRing.ResidueGenerator
lake build FLT.GroupScheme.LocalIntegralPowerBasis
```

Build logs: `/tmp/r5c-{monogenic,residue,local}-build.log`.
Each corresponding `/tmp/r5c-{monogenic,residue,local}-axioms.lean` scratch
file was run with `lake env lean`; its `.log` records `#print axioms` for
all nine declarations (eight theorems and the chosen power-basis definition),
using only `propext`, `Classical.choice`, and `Quot.sound`, and all 15 enabled
linters passing. The local scratch file also checks both requested targets
for `LocalPointField M` explicitly.

`git diff --check` passes. The 657 unique imports in `FLT.lean`, sorted with
`LC_ALL=C`, match exactly the 657 `.lean` files under `FLT/`. The three new
modules contain no prohibited proof escapes. Only new files and `FLT.lean`
were changed; the inherited untracked plan and prior gap reports were left alone.

No R5c blocker remains. This discharges step 1 of `PREV_BLOCKED.md`; it does
not prove the Fontaine bound. Step 2 remains: control differentials or
ramification of the full point field from `KilledBy 3 M`, including the
strict endpoint and passage from point-image algebras to the full integers.
The parent R5b bead must remain open for that separate arithmetic argument.
