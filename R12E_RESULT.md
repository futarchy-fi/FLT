# R12e completed

Checked at 2026-09-28 09:16:38 UTC on `task/r12e`.
Code commits: `4aeea5d1`, `4c6c6e22`; local only, no push.

Proved all three requested endpoints:

- `ThreeAdicPlan.primePowerSortedExtensionExists`
- `ThreeAdicPlan.threeAdicCharacterPurity`
- `PNat.pow_add_pow_ne_pow_of_three_inputs`

The classification `simpleDThree` supplies a canonical integral factor
filtration. The existing `sortCanonicalFactors` and
`sortedExtensionOfConstantThenMultiplicative` construct its sorted extension
without a killed-by-three assumption. Thus the general endpoint follows
directly, preserving all existing integral extension data.

Verification:

- `lake build FLT.Assembly.PrimePowerSortingProof`: passed.
- `lake build FLT.Assembly.ThreeInputFinal`: passed.
- `lake build FLT`: passed, 9963 jobs; `/tmp/r12e-full-build.log`.
- Each new module passed `lake env
  .lake/packages/batteries/.lake/build/bin/runLinter --no-build MODULE`.
  Logs: `/tmp/r12e-sorting-lint.log`, `/tmp/r12e-final-lint.log`.
- Kernel dependency queries for all three endpoints returned exactly
  `propext`, `Classical.choice`, and `Quot.sound`.
  Evidence: `/tmp/r12e-dependencies.log`.
- `python3 /tmp/r12e-verify-source.py`: passed. All 985 root imports are sorted
  and match every Lean file under `FLT/`; both new modules satisfy the source
  restrictions and the 100-character line limit.
- `git diff --check 94488eba HEAD`: passed.

Only new files and the two sorted imports in `FLT.lean` changed.
Supplied untracked notes were left untouched. No blockers remain.
The durable proof-route note is local hub commit `5e4acf41` in
`/srv/agent-data/home/workspaces/fermat/r12e-hub-log`, branch
`memory/r12e-sorting-20260928`; it was not pushed.
