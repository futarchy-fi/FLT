/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedProjChartPullback
public import FLT.Mazur.GradedProjUnitChartMap

/-!
# Homogeneous fraction evaluation after line-bundle pullback

The two evaluations agree by transporting the numerator-denominator equation
through tensor-power pullback and cancelling the invertible denominator.
No compatibility of the chosen line coordinates is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open Scheme.Modules
namespace FLT.Mazur.SectionGradedProjPullbackEvaluation
open FCurve ModuleLineBundleTensorPullback SectionGradedSum
open SectionGradedCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y Z : Scheme} (p : Y ⟶ X) (k : Z ⟶ Y) (L : X.Modules)

/-- A scalar equation on twice-pulled tensor sections is an equation on the composite pullback. -/
lemma scalar_equation_comp (n : ℕ) (s t : Γ(tensorPower L n, ⊤)) (a : Γ(Z, ⊤))
    (he : a • pullGlobal k (tensorPower ((pullback p).obj L) n)
        (SectionGradedPullback.pull p L n ⊤ s) =
      pullGlobal k (tensorPower ((pullback p).obj L) n)
        (SectionGradedPullback.pull p L n ⊤ t)) :
    a • pullGlobal (k ≫ p) (tensorPower L n) s =
      pullGlobal (k ≫ p) (tensorPower L n) t := by
  have hb : a • pullGlobal k ((pullback p).obj (tensorPower L n))
      (pullGlobal p (tensorPower L n) s) =
        pullGlobal k ((pullback p).obj (tensorPower L n))
          (pullGlobal p (tensorPower L n) t) := by
    apply (ConcreteCategory.bijective_of_isIso
      (((pullback k).map (tensorPowerIso p L n).hom).app ⊤)).injective
    rw [Hom.app_smul, pullGlobal_naturality, pullGlobal_naturality]
    exact he
  have hc := congrArg (((pullbackComp k p).hom.app (tensorPower L n)).app ⊤) hb
  rwa [Hom.app_smul, pullGlobal_comp_hom, pullGlobal_comp_hom] at hc

variable [hL : Fact (LocallyFreeRankOne L)]

/-- Pullback preserves the line-bundle condition. -/
local instance pulledLine : Fact (LocallyFreeRankOne ((pullback p).obj L)) :=
  ⟨hL.out.pullback p⟩

/-- Evaluating a pulled homogeneous fraction agrees with evaluation on the composite domain. -/
lemma evaluation_map
    (e : (pullback k).obj ((pullback p).obj L) ≅ structureModule Z)
    (e' : (pullback (k ≫ p)).obj L ≅ structureModule Z)
    (f : SectionGradedSum.Sections L ⊤)
    (hf : IsUnit (SectionGradedProjChart.ringHom k ((pullback p).obj L) e
      (SectionGradedPullback.ringHom p L f)))
    (hf' : IsUnit (SectionGradedProjChart.ringHom (k ≫ p) L e' f)) :
    (SectionGradedProjChart.evaluation k ((pullback p).obj L) e
      (SectionGradedPullback.ringHom p L f) hf).comp
        (Away.map (SectionGradedPullback.gradedRingHom p L) f) =
      SectionGradedProjChart.evaluation (k ≫ p) L e' f hf' := by
  ext z
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  obtain ⟨s, hs⟩ := c.den.property
  obtain ⟨t, ht⟩ := c.num.property
  let φ := SectionGradedPullback.gradedRingHom p L
  have hw : Submonoid.powers f ≤ (Submonoid.powers (φ f)).comap φ := by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, by simp⟩
  let c' := c.map φ hw
  have hs' : of ((pullback p).obj L) ⊤ c'.deg
      (SectionGradedPullback.pull p L c.deg ⊤ s) = c'.den := by
    change _ = SectionGradedPullback.ringHom p L c.den
    rw [← hs]
    exact (SectionGradedPullback.sumMap_of p L c.deg s).symm
  have ht' : of ((pullback p).obj L) ⊤ c'.deg
      (SectionGradedPullback.pull p L c.deg ⊤ t) = c'.num := by
    change _ = SectionGradedPullback.ringHom p L c.num
    rw [← ht]
    exact (SectionGradedPullback.sumMap_of p L c.deg t).symm
  have he := SectionGradedProjChart.evaluation_mk_pullGlobal k ((pullback p).obj L) e
    (φ f) hf c' _ _ hs' ht'
  have hb := scalar_equation_comp p k L c.deg s t _ he
  have hc := congrArg ((tensorPowerIso (k ≫ p) L c.deg).hom.app ⊤) hb
  rw [Hom.app_smul] at hc
  have hd := (SectionGradedCoordinateEvaluation.coordinate_equation_iff
    e' ⊤ c.deg _ _ _).mpr hc
  apply (GradedProjUnitChart.denominator_isUnit
    (grade L ⊤) (SectionGradedProjChart.ringHom (k ≫ p) L e') f hf' c).mul_left_inj.mp
  change SectionGradedProjChart.evaluation k ((pullback p).obj L) e (φ f) hf
    (HomogeneousLocalization.mk c') * SectionGradedProjChart.ringHom (k ≫ p) L e' c.den =
      GradedProjUnitChart.evaluation (grade L ⊤)
        (SectionGradedProjChart.ringHom (k ≫ p) L e') f hf'
          (HomogeneousLocalization.mk c) * SectionGradedProjChart.ringHom (k ≫ p) L e' c.den
  rw [GradedProjUnitChart.evaluation_mk_mul]
  rw [← hs, ← ht, SectionGradedProjChart.ringHom_of, SectionGradedProjChart.ringHom_of]
  exact hd

omit hL in
/-- A generator on the composite domain also generates after the tensor-power comparison. -/
lemma ringHom_isUnit_pull_section
    (e : (pullback k).obj ((pullback p).obj L) ≅ structureModule Z)
    (e' : (pullback (k ≫ p)).obj L ≅ structureModule Z)
    {d : ℕ} (s : Γ(tensorPower L d, ⊤))
    (hs : IsUnit (SectionGradedProjChart.ringHom (k ≫ p) L e' (of L ⊤ d s))) :
    IsUnit (SectionGradedProjChart.ringHom k ((pullback p).obj L) e
      (of ((pullback p).obj L) ⊤ d (SectionGradedPullback.pull p L d ⊤ s))) := by
  have := SectionGradedProjChart.pullGenerator_isIso_of_ringHom (k ≫ p) L e' s hs
  have hi := globalSectionHom_isIso_transport _ ((pullbackComp k p).app
    (tensorPower L d)).symm (pullGlobal (k ≫ p) (tensorPower L d) s)
  change IsIso (globalSectionHom _
    (((pullbackComp k p).inv.app (tensorPower L d)).app ⊤
      (pullGlobal (k ≫ p) (tensorPower L d) s))) at hi
  rw [pullGlobal_comp] at hi
  have hi' : IsIso (globalSectionHom ((pullback k).obj ((pullback p).obj (tensorPower L d)))
    (pullGlobal k _ (pullGlobal p (tensorPower L d) s))) := hi
  have hj := globalSectionHom_isIso_transport _
    ((pullback k).mapIso (tensorPowerIso p L d))
      (pullGlobal k _ (pullGlobal p (tensorPower L d) s))
  change IsIso (globalSectionHom _
    (((pullback k).map (tensorPowerIso p L d).hom).app ⊤
      (pullGlobal k _ (pullGlobal p (tensorPower L d) s)))) at hj
  rw [pullGlobal_naturality] at hj
  have hj' : IsIso (globalSectionHom ((pullback k).obj (tensorPower ((pullback p).obj L) d))
    (pullGlobal k _ (SectionGradedPullback.pull p L d ⊤ s))) := hj
  exact SectionGradedProjChart.ringHom_isUnit_of_pullGenerator k ((pullback p).obj L) e
    (SectionGradedPullback.pull p L d ⊤ s)

/-- Local canonical maps commute with a globally defined section-ring Proj pullback. -/
@[reassoc]
lemma toProj_map
    (e : (pullback k).obj ((pullback p).obj L) ≅ structureModule Z)
    (e' : (pullback (k ≫ p)).obj L ≅ structureModule Z)
    (hφ : HomogeneousIdeal.irrelevant (grade ((pullback p).obj L) ⊤) ≤
      (HomogeneousIdeal.irrelevant (grade L ⊤)).map
        (SectionGradedPullback.gradedRingHom p L))
    {d : ℕ} (s : Γ(tensorPower L d, ⊤)) (hd : 0 < d)
    (hs : IsUnit (SectionGradedProjChart.ringHom k ((pullback p).obj L) e
      (SectionGradedPullback.ringHom p L (of L ⊤ d s))))
    (hs' : IsUnit (SectionGradedProjChart.ringHom (k ≫ p) L e' (of L ⊤ d s))) :
    SectionGradedProjChart.toProj k ((pullback p).obj L) e
      (SectionGradedPullback.ringHom p L (of L ⊤ d s)) hs
      (SectionGradedPullback.ringHom_mem_grade p L ⟨s, rfl⟩) hd ≫
        Proj.map (SectionGradedPullback.gradedRingHom p L) hφ =
      SectionGradedProjChart.toProj (k ≫ p) L e' (of L ⊤ d s) hs' ⟨s, rfl⟩ hd := by
  unfold SectionGradedProjChart.toProj GradedProjUnitChart.toProj
  rw [Category.assoc]
  erw [Proj.awayι_comp_map _ hφ hd _ ⟨s, rfl⟩]
  rw [← Category.assoc]
  congr 1
  unfold GradedProjUnitChart.toAffine
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun v ↦ Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom v))
    (evaluation_map p k L e e' _ hs hs')

end FLT.Mazur.SectionGradedProjPullbackEvaluation
