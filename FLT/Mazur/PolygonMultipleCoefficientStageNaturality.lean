/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonMultipleCoefficientUnitChart
public import FLT.Mazur.PolygonMultipleStageGeneratingCover

/-!
# Complete coefficient comparison retains every original stage

Pulling back the original generating cover gives genuine invertible coordinates.
The unit-chart identity then proves the global morphism identity on each stage.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve ModuleLineBundleTensorPullback SectionGradedSum
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] compatibleEval boundaryLine family originalStageToMultipleProj
variable {K L : Type} [Field K] [Field L] (f : K →+* L) (n : ℕ) (h : 2 ≤ n)
  [NeZero n] (q : ℕ) [NeZero q]
  (hK : exactVeroneseStep K n h ∣ q) (hL : exactVeroneseStep L n h ∣ q)

/-- The complete coefficient morphism agrees with the actual coefficient morphism on every stage. -/
@[reassoc]
theorem originalStageToMultipleProj_coefficient (m : ℕ) :
    originalStageToMultipleProj L n h q hL m ≫ multipleCoefficientProjMap f n h q hK hL =
      stageCoefficientFamily f m n h ≫ originalStageToMultipleProj K n h q hK m := by
  obtain ⟨𝒰, c, d, s, hs, hd, hu⟩ := exists_multipleStageGeneratingCover K n h q hK m
  let p := stageCoefficientFamily f m n h
  apply Scheme.Cover.hom_ext (𝒰.pullback₁ p)
  intro i
  let k := CategoryTheory.Limits.pullback.fst p (𝒰.f i)
  let l := CategoryTheory.Limits.pullback.snd p (𝒰.f i)
  have hc : k ≫ p = l ≫ 𝒰.f i := CategoryTheory.Limits.pullback.condition
  let c' : (pullback (k ≫ p)).obj (boundaryLine K m n h) ≅ structureModule _ := by
    rw [hc]
    exact SectionGradedProjChart.pullTrivialization (𝒰.f i) (boundaryLine K m n h) (c i) l
  let c'' := (pullback k).mapIso (coefficientBoundaryLineIso f m n h).symm ≪≫
    (pullbackComp k p).app (boundaryLine K m n h) ≪≫ c'
  obtain ⟨t, ht⟩ := (boundaryVeroneseEvaluation K n h q m).map_mem (hs i)
  change of (boundaryLine K m n h) ⊤ (q * d i) t =
    compatibleVeroneseEval K n h q m (s i) at ht
  have hi : IsIso (globalSectionHom _ (pullGlobal (k ≫ p)
      (tensorPower (boundaryLine K m n h) (q * d i)) t)) := by
    rw [hc]
    apply SectionGradedProjChart.pullGenerator_isIso_of_ringHom _ (boundaryLine K m n h)
      (SectionGradedProjChart.pullTrivialization (𝒰.f i) (boundaryLine K m n h) (c i) l) t
    exact SectionGradedProjChart.ringHom_isUnit_pullback (𝒰.f i) (boundaryLine K m n h)
      (c i) l _ t (by rw [ht]; exact hu i)
  have hv : IsUnit (SectionGradedProjChart.ringHom (k ≫ p) (boundaryLine K m n h) c'
      (compatibleVeroneseEval K n h q m (s i))) := by
    rw [← ht]
    exact SectionGradedProjChart.ringHom_isUnit_of_pullGenerator (k ≫ p) _ c' t
  change k ≫ (_ ≫ _) = k ≫ (p ≫ _)
  rw [← Category.assoc k p]
  exact multipleCoefficientProjMap_unit f n h q m k c'' c' hK hL (s i) (hs i) (hd i) hv

end FLT.Mazur.PolygonInfinitesimalStages
