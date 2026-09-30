# B18-SERRE boundary

The absolute and relative proof split is in `SERRE_SPLIT.md`.
This is the boundary for the relative endpoint, not a claim that the
main-only work is blocked.

## Exact missing prerequisites

1. **B17-FINAL, rows 11c-13:** actual pullback/tensor and affine projective
   base-change API, the common Chow line sheaf, both relative very ample
   presentations, and compatible identifications of every natural power
   with the restriction of O(n), including n=0. The source modules belong
   to `../wt-r1e`; this lane does not edit them.
2. **Closed line projection formula (split leaf 5):** prove the canonical
   tensor/direct-image comparison is invertible for the B17 pullback of a
   locally free line. No such isomorphism may be accepted as a hypothesis.
   Leaf 6 then transfers absolute Serre vanishing to closed projective
   embeddings.
3. **Uniform localized presentation tower (leaf 8):** transport one fixed
   finite tower to every principal base open, preserving degrees and
   exactness, using B17's affine base-change coefficient comparisons.
   Choosing separate absolute Serre bounds on infinitely many principal
   opens is not a uniform relative bound. Leaf 9 performs the resulting
   vanishing induction on every principal subopen.
4. **B18 5c-6a:** actual higher images must be identified with sheafification
   of the open cohomology presheaf, with module scalars and open restriction
   retained. Leaf 10 uses basis-local vanishing to prove actual affine
   higher-image zero; leaf 11 takes a maximum on a finite affine base cover.
5. **Full row 8:** leaf 12 applies leaf 11 to both B17 presentations and
   takes their maximum. B18 6b is then needed for the relative composition
   comparison application, but is not an input to the maximum step.

The bounded statement sketches, modules, existing lemmas and dependency
edges for each remaining leaf are in `SERRE_SPLIT.md`. In particular,
absolute cohomology finiteness is not Serre vanishing, and whole-affine
cohomology vanishing alone is not higher-direct-image vanishing.

## Read-only checks

Checked 2026-09-30 in this checkout and the lane briefs:

```
git ls-files 'FLT/Mazur/ModulePullback*' 'FLT/Mazur/RelativeVeryAmple*' 'FLT/Mazur/HigherDirectImagePresheaf*'
cat ../wt-r1e/BRIEF.md ../wt-r5a/BRIEF.md
rg -n 'theorem|lemma|def ' FLT/Mazur/ProjectiveCoherentCohomology.lean
```

The first check returns no matching tracked modules here; the briefs
assign these missing contracts to the other lanes. No B17/B18-owned
module was modified, no vanishing was added to an assumption record,
and nothing was pushed. Final main-only validation is recorded separately
at the end of `SERRE_SPLIT.md` once its checks finish.
