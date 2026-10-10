/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RetainedSubringGradedMap
public import FLT.Mazur.SectionRetainedFractionUniqueness
public import FLT.Mazur.SectionLinePullbackFraction

/-!
# Retained fractions under the original line pullback comparison

The retained map applies the specified section pullback. Its fraction
values agree with evaluation on the composite scheme morphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules HomogeneousLocalization

namespace FLT.Mazur.SectionRetainedLineEvaluation

open FCurve ModuleLineBundleTensorPullback SectionGradedSum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] ModuleSheafTensor.tensor

variable {X Y Z : Scheme} (p : Y ⟶ X) (L : X.Modules) (M : Y.Modules)
  [hL : Fact (LocallyFreeRankOne L)] [Fact (LocallyFreeRankOne M)]
  (e : (pullback p).obj L ≅ M) (q : ℕ)

local instance pulledLine : Fact (LocallyFreeRankOne ((pullback p).obj L)) :=
  ⟨hL.out.pullback p⟩

/-- The retained graded map is the restriction of actual pullback and line transport. -/
def map : RetainedSubringGrading.grade (grade L ⊤) q →+*ᵍ
    RetainedSubringGrading.grade (grade M ⊤) q :=
  RetainedSubringGradedMap.map _ _
    ((SectionGradedIso.gradedRingHom e ⊤).comp (SectionGradedPullback.gradedRingHom p L)) q

/-- The retained map keeps the original tensor-degree section transport. -/
theorem map_insertion (d : ℕ) (s : Γ(tensorPower L (q * d), ⊤)) :
    map p L M e q (SectionRetainedChartComparison.insertion L q d s) =
      SectionRetainedChartComparison.insertion M q d
        (SectionGradedLinePullback.sectionMap p e (q * d) ⊤ s) := by
  apply Subtype.ext
  exact SectionGradedLinePullback.ringHom_of p e (q * d) s

/-- Every retained value is the original line pullback on the underlying full section ring. -/
theorem map_val (a : RetainedSubringGrading.ring (grade L ⊤) q) :
    (map p L M e q a).val = SectionGradedLinePullback.ringHom p e a.val := rfl

/-- Homogeneous presentations keep the prescribed original section after retained transport. -/
theorem map_homogeneous_value {d : ℕ} (a : RetainedSubringGrading.ring (grade L ⊤) q)
    (s : Γ(tensorPower L d, ⊤)) (hs : of L ⊤ d s = a.val) :
    of M ⊤ d (SectionGradedLinePullback.sectionMap p e d ⊤ s) = (map p L M e q a).val := by
  rw [map_val, ← hs]
  exact (SectionGradedLinePullback.ringHom_of p e d s).symm

attribute [local irreducible] map SectionGradedLinePullback.ringHom

variable [GradedRing (RetainedSubringGrading.grade (grade L ⊤) q)]
  [GradedRing (RetainedSubringGrading.grade (grade M ⊤) q)]
  (k : Z ⟶ Y) (c : (pullback k).obj M ≅ structureModule Z)
  (c' : (pullback (k ≫ p)).obj L ≅ structureModule Z)

/-- Evaluation of every retained fraction commutes with the specified line pullback. -/
theorem evaluation_map (f : RetainedSubringGrading.ring (grade L ⊤) q)
    (hf : IsUnit (SectionRetainedProjChart.ringHom k M c q (map p L M e q f)))
    (hf' : IsUnit (SectionRetainedProjChart.ringHom (k ≫ p) L c' q f)) :
    (GradedProjUnitChart.evaluation _ (SectionRetainedProjChart.ringHom k M c q)
      (map p L M e q f) hf).comp (Away.map (map p L M e q) f) =
      GradedProjUnitChart.evaluation _ (SectionRetainedProjChart.ringHom (k ≫ p) L c' q)
        f hf' := by
  ext z
  obtain ⟨a, rfl⟩ := HomogeneousLocalization.mk_surjective z
  obtain ⟨s, hs⟩ := a.den.property
  obtain ⟨t, ht⟩ := a.num.property
  let φ := map p L M e q
  have hw : Submonoid.powers f ≤ (Submonoid.powers (φ f)).comap φ := by
    rintro _ ⟨i, rfl⟩
    exact ⟨i, by simp⟩
  let b := a.map φ hw
  have hs' := map_homogeneous_value p L M e q a.den.val s hs
  have ht' := map_homogeneous_value p L M e q a.num.val t ht
  have he := SectionRetainedFractionEquation.evaluation_mk k M c q (φ f) hf b rfl _ _ hs' ht'
  have hb := SectionLinePullbackFraction.scalar_equation p k L M e (q * a.deg) s t _ he
  exact SectionRetainedFractionUniqueness.eq_evaluation (k ≫ p) L c' q f hf' a
    s t hs ht _ hb

/-- Local retained Proj charts commute with the map of the actual retained section rings. -/
@[reassoc]
theorem toProj_map
    (hφ : HomogeneousIdeal.irrelevant (RetainedSubringGrading.grade (grade M ⊤) q) ≤
      (HomogeneousIdeal.irrelevant (RetainedSubringGrading.grade (grade L ⊤) q)).map
        (map p L M e q))
    {d : ℕ} (s : Γ(tensorPower L (q * d), ⊤)) (hd : 0 < d)
    (hs : IsUnit (SectionRetainedProjChart.ringHom k M c q
      (map p L M e q (SectionRetainedChartComparison.insertion L q d s))))
    (hs' : IsUnit (SectionRetainedProjChart.ringHom (k ≫ p) L c' q
      (SectionRetainedChartComparison.insertion L q d s))) :
    SectionRetainedProjChart.toProj k M c q
      (map p L M e q (SectionRetainedChartComparison.insertion L q d s)) hs
      ((map p L M e q).map_mem (SectionRetainedChartComparison.insertion_mem L q d s)) hd ≫
        Proj.map (map p L M e q) hφ =
      SectionRetainedProjChart.toProj (k ≫ p) L c' q
        (SectionRetainedChartComparison.insertion L q d s) hs'
        (SectionRetainedChartComparison.insertion_mem L q d s) hd := by
  unfold SectionRetainedProjChart.toProj GradedProjUnitChart.toProj
  rw [Category.assoc]
  erw [Proj.awayι_comp_map _ hφ hd _ (SectionRetainedChartComparison.insertion_mem L q d s)]
  rw [← Category.assoc]
  congr 1
  unfold GradedProjUnitChart.toAffine
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun v ↦ Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom v))
    (evaluation_map p L M e q k c c' _ hs hs')

end FLT.Mazur.SectionRetainedLineEvaluation
