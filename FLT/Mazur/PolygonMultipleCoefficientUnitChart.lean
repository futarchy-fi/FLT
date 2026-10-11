/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonMultipleCoefficientProjMap
public import FLT.Mazur.PolygonMultipleStageUnitChart
public import FLT.Mazur.SectionRetainedSourceLineEvaluation
public import FLT.Mazur.GradedDegreeProjUnitNaturality

/-!
# Coefficient comparison on original unit coordinates

The complete coefficient morphism retains original line-coordinate evaluations,
with arbitrary trivializations of the pulled-back boundary lines.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve ModuleLineBundleTensorPullback SectionGradedSum
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] compatibleEval boundaryLine family
variable {K L : Type} [Field K] [Field L] (f : K →+* L) (n : ℕ) (h : 2 ≤ n)
  (q : ℕ) [NeZero q] (m : ℕ) {Z : Scheme}
  (k : Z ⟶ (family L m n h).left)
  (c : (pullback k).obj (boundaryLine L m n h) ≅ structureModule Z)
  (c' : (pullback (k ≫ stageCoefficientFamily f m n h)).obj (boundaryLine K m n h) ≅
    structureModule Z)

omit [NeZero q] in
/-- An original compatible generator remains invertible under actual coefficient pullback. -/
theorem compatibleCoefficient_unit {d : ℕ} (s : CompatibleVeroneseSections K n h q)
    (hs : s ∈ compatibleVeroneseGrade K n h q d)
    (hu : IsUnit (SectionGradedProjChart.ringHom (k ≫ stageCoefficientFamily f m n h)
      (boundaryLine K m n h) c' (compatibleVeroneseEval K n h q m s))) :
    IsUnit (SectionGradedProjChart.ringHom k (boundaryLine L m n h) c
      (compatibleVeroneseEval L n h q m (compatibleVeroneseCoefficientMap f n h q s))) := by
  obtain ⟨t, ht⟩ := (boundaryVeroneseEvaluation K n h q m).map_mem hs
  change of (boundaryLine K m n h) ⊤ (q * d) t = compatibleVeroneseEval K n h q m s at ht
  rw [compatibleVeroneseCoefficientMap_eval, ← ht, coefficientBoundarySections_of]
  rw [← ht] at hu
  exact SectionLinePullbackFraction.ringHom_isUnit_section _ k _ _
    (coefficientBoundaryLineIso f m n h) c c' t hu

/-- The local source chart keeps the original coefficient evaluation after line transport. -/
theorem compatibleCoefficient_unit_source {d : ℕ} (s : CompatibleVeroneseSections K n h q)
    (hs : s ∈ compatibleVeroneseGrade K n h q d) (hd : 0 < d)
    (hu : IsUnit (SectionGradedProjChart.ringHom (k ≫ stageCoefficientFamily f m n h)
      (boundaryLine K m n h) c' (compatibleVeroneseEval K n h q m s))) :
    GradedProjUnitChart.toProj (compatibleVeroneseGrade K n h q)
        (((SectionGradedProjChart.ringHom k (boundaryLine L m n h) c).comp
          (compatibleVeroneseEval L n h q m)).comp (compatibleVeroneseCoefficientMap f n h q))
        s (compatibleCoefficient_unit f n h q m k c c' s hs hu) hs hd =
      GradedProjUnitChart.toProj (compatibleVeroneseGrade K n h q)
        ((SectionGradedProjChart.ringHom (k ≫ stageCoefficientFamily f m n h)
          (boundaryLine K m n h) c').comp (compatibleVeroneseEval K n h q m)) s hu hs hd := by
  let _ : GradedRing (RetainedSubringGrading.grade
      (grade (boundaryLine K m n h) ⊤) q) :=
    boundaryVeroneseGradedRing K n h q (NeZero.pos q) m
  let _ : GradedRing (RetainedSubringGrading.grade
      (grade (boundaryLine L m n h) ⊤) q) :=
    boundaryVeroneseGradedRing L n h q (NeZero.pos q) m
  have he : ((SectionGradedProjChart.ringHom k (boundaryLine L m n h) c).comp
        (compatibleVeroneseEval L n h q m)).comp (compatibleVeroneseCoefficientMap f n h q) =
      (((SectionRetainedProjChart.ringHom k (boundaryLine L m n h) c q).comp
        (SectionRetainedLineEvaluation.map (stageCoefficientFamily f m n h)
          (boundaryLine K m n h) (boundaryLine L m n h)
          (coefficientBoundaryLineIso f m n h) q).toRingHom).comp
        (boundaryVeroneseEvaluation K n h q m).toRingHom) := by
    apply RingHom.ext
    intro a
    change SectionGradedProjChart.ringHom k (boundaryLine L m n h) c
      (compatibleVeroneseEval L n h q m (compatibleVeroneseCoefficientMap f n h q a)) = _
    rw [compatibleVeroneseCoefficientMap_eval]
    rfl
  simp only [he]
  exact SectionRetainedSourceLineEvaluation.toProj_source _ _ _
    (coefficientBoundaryLineIso f m n h) q k c c' _
    (boundaryVeroneseEvaluation K n h q m) s hs hd _ hu

variable [NeZero n] (hK : exactVeroneseStep K n h ∣ q) (hL : exactVeroneseStep L n h ∣ q)

include c in
/-- On each original unit chart the global coefficient map is the original stage pullback. -/
@[reassoc]
theorem multipleCoefficientProjMap_unit {d : ℕ} (s : CompatibleVeroneseSections K n h q)
    (hs : s ∈ compatibleVeroneseGrade K n h q d) (hd : 0 < d)
    (hu : IsUnit (SectionGradedProjChart.ringHom (k ≫ stageCoefficientFamily f m n h)
      (boundaryLine K m n h) c' (compatibleVeroneseEval K n h q m s))) :
    k ≫ originalStageToMultipleProj L n h q hL m ≫
        multipleCoefficientProjMap f n h q hK hL =
      (k ≫ stageCoefficientFamily f m n h) ≫ originalStageToMultipleProj K n h q hK m := by
  have hv := compatibleCoefficient_unit f n h q m k c c' s hs hu
  rw [← Category.assoc, originalStageToMultipleProj_unit L n h q hL m k c
    (compatibleVeroneseCoefficientMap f n h q s)
    ((compatibleVeroneseCoefficientGradedMap f n h q).map_mem hs) hd hv,
    originalStageToMultipleProj_unit K n h q hK m _ c' s hs hd hu]
  unfold multipleCoefficientProjMap
  have he := GradedDegreeProjUnitNaturality.toProj_map _ _ _ 1
    (compatibleVeroneseCoefficientMap_mem_scaled f n h q) Nat.zero_lt_one
    (coefficientImage_complete_cover f n h q hK hL)
    ((SectionGradedProjChart.ringHom k (boundaryLine L m n h) c).comp
      (compatibleVeroneseEval L n h q m)) s hs hd hv
  simp only [Nat.one_mul] at he
  rw [he]
  exact compatibleCoefficient_unit_source f n h q m k c c' s hs hd hu

end FLT.Mazur.PolygonInfinitesimalStages
