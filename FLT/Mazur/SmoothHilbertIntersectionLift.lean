/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothHilbertIntersectionComponents

/-!
# Universal lifts to the assembled Hilbert intersection

A compatible pair on an arbitrary original test lifts uniquely. The lift is
constructed on the actual component inverse images and glued as a scheme map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel FCurve SchemePicard OrderedCurvePower
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {B : X.Modules} (hB : AmpleLineBundle B)
  (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))
  {U : Over (Spec (.of R))} (k : U ⟶ smoothHilbertSource f) (b : U ⟶ T)
  (hk : (relativeFppfSheaf f).obj.map k.op (smoothHilbertSourceSection f hB) =
    (relativeFppfSheaf f).obj.map b.op s)

include hk

/-- On every actual component inverse image, the chart point has the required class. -/
theorem smoothHilbertIntersection_local_class (i : SmoothHilbertTranslationIndex) :
    smoothHilbertPoint f hB i _
      (relativeCoproductPullToComponent (smoothHilbertTest f) k i) =
        (relativeFppfSheaf f).obj.map
          (relativeCoproductPullToDomain (smoothHilbertTest f) k i ≫ b).op s := by
  rw [← smoothHilbertSourceSection_chart]
  change (relativeFppfSheaf f).obj.map
    (relativeCoproductPullToComponent (smoothHilbertTest f) k i ≫
      relativeCoproductArrow (smoothHilbertTest f) i).op _ = _
  rw [← relativeCoproductPull_square]
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  exact congrArg ((relativeFppfSheaf f).obj.map
    (relativeCoproductPullToDomain (smoothHilbertTest f) k i).op) hk

/-- Every compatible pair lifts uniquely, even if it meets multiple source components. -/
theorem smoothHilbertIntersection_lift :
    ∃! l : U ⟶ smoothHilbertIntersectionSource f hB T s,
      l ≫ smoothHilbertIntersectionToSource f hB T s = k ∧
        l ≫ smoothHilbertIntersectionToTest f hB T s = b := by
  have H (i : SmoothHilbertTranslationIndex) :=
    variableHilbertOverlap_lift f i.2 hB _ _ T s
      (relativeCoproductPullToDomain (smoothHilbertTest f) k i ≫ b)
      (relativeCoproductPullToComponent (smoothHilbertTest f) k i)
      (smoothHilbertIntersection_local_class f hB T s k b hk i)
  choose l hl hu using H
  let g i := l i ≫ relativeCoproductArrow (fun j ↦ smoothHilbertOverlap f hB j T s) i
  let q := relativeCoproductPullGlue (smoothHilbertTest f) k g
  have hq (i : SmoothHilbertTranslationIndex) :
      relativeCoproductPullToDomain (smoothHilbertTest f) k i ≫ q = g i :=
    relativeCoproductPullGlue_map (smoothHilbertTest f) k g i
  have hc : q ≫ smoothHilbertIntersectionToSource f hB T s = k := by
    apply relativeCoproductPull_hom_ext (smoothHilbertTest f) k
    intro i
    rw [← Category.assoc, hq]
    change (l i ≫ _) ≫ _ = _
    rw [Category.assoc, smoothHilbertIntersectionToSource_chart, ← Category.assoc]
    have hli := (hl i).2
    change l i ≫ smoothHilbertOverlapToChart f hB i T s = _ at hli
    rw [hli]
    exact (relativeCoproductPull_square (smoothHilbertTest f) k i).symm
  have ht : q ≫ smoothHilbertIntersectionToTest f hB T s = b := by
    apply relativeCoproductPull_hom_ext (smoothHilbertTest f) k
    intro i
    rw [← Category.assoc, hq]
    change (l i ≫ _) ≫ _ = _
    rw [Category.assoc, smoothHilbertIntersectionToTest_chart]
    exact (hl i).1
  exact ⟨q, ⟨hc, ht⟩, fun m hm ↦ smoothHilbertIntersection_hom_ext f hB T s
    (hm.1.trans hc.symm) (hm.2.trans ht.symm)⟩

end FLT.Mazur.HilbertChart
