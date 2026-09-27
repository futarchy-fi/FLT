# R1e: module patching complete; global Hopf models remain open

The delivered fallback is `ThreeAdicPlan.PadicPatching.module_patch_away_two`
in `FLT/GroupScheme/PadicModulePatching.lean`. It patches an arbitrary finite
projective `ℤ[1/6]`-module and an arbitrary finitely generated full `ℤ₃`-lattice
in its local generic fibre to a finite projective `ℤ[1/2]`-module. The result
contains both base-change isomorphisms and their compatibility over `ℚ₃`.
The local lattice need not have a rational basis.

`patchModule` proves the same assertion for a prime `p` and `ℤ[1/d]`, with
`p ∤ d`. `Base d` is `Localization.Away d`; `Away d p` first inverts `d`, then
`p`. `awayEquivSingle` identifies it with `Localization.Away (d * p)`.
`baseOneEquivInt` identifies `Base 1` with `ℤ`.

The proofs construct the intersection, bound its denominators, prove finite
projectivity, clear powers of `p` for the away comparison, and use integral
approximation for the local comparison. Injectivity of the local comparison
uses flatness. No existence or base-change conclusion is assumed.

## Exact remaining gap

Neither `global_model_away_two` nor `global_model_over_int` is proved here.
Their completion requires:

1. A bialgebra comparison between the `ℚ₃`-base change of
   `W.GenericCoordinateAlgebra` and `W.localAtThree.GenericCoordinateAlgebra`,
   respecting the chosen absolute-Galois restriction. The existing
   `HasFiniteFlatModel.genericBialgEquiv` compares models over the *same*
   fraction field; it does not alone supply this change-of-field comparison.
   Combine that comparison with `h3.genericBialgEquiv` to embed the local
   coordinate algebra as the full lattice used by `patchModule`.
2. Functorial and tensor-compatible descent for the module patch. In
   particular, identify the patched tensor square with the intersection of
   the away and local tensor squares. This is needed to restrict
   comultiplication to `H → H ⊗ H`; scalar intersection alone does not prove
   that inclusion.
3. Descend multiplication, unit, comultiplication, counit and antipode, prove
   the Hopf identities and cocommutativity, and make the generic comparison
   a bialgebra equivalence. Finite projectivity already supplies the module
   finiteness and flatness once these algebraic structures are installed.
4. Transport from the displayed localization realizations to the existing
   model records, then use `HasFiniteFlatModel.ofGenericBialgEquiv` for the
   required Galois-equivariant point identification.

Thus the remaining obstruction is Hopf-algebra descent and the arithmetic
comparison connecting its two inputs, not module existence or either of its
base changes. No placeholder global-model declaration is included.

## Verification

Re-run the four targeted builds (no aggregate `FLT` build):

```sh
lake build FLT.GroupScheme.PadicPatchingArithmetic FLT.GroupScheme.PadicPatchingRings FLT.GroupScheme.PadicLatticePatching FLT.GroupScheme.PadicModulePatching
lake lint -- --no-build FLT.GroupScheme.PadicModulePatching
```

Checked at 2026-09-27 22:44:23 UTC: the four targeted builds and lint passed.
`lake env lean /tmp/R1eAllAxioms.lean` checked all 37 explicit theorem/definition
declarations; every dependency list contains only `propext`, `Classical.choice`,
and `Quot.sound` (log: `/tmp/R1eAllAxioms.log`). The sorted root-import set
exactly matches all 614 files under `FLT/`.
`FLT.lean` imports all four new modules in sorted order. `PLAN.ref.md` was an
untracked input supplied with the worktree and is not part of the change.
