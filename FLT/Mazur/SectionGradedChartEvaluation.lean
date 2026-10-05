/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedChartRatios
public import FLT.Mazur.SectionGradedProjChartPullback
public import FLT.Mazur.ModuleSectionRatioOpenPullback

/-!
# The intrinsic chart comparison agrees with coordinate evaluation

On a trivializing open immersion, the comparison's fraction ratio pulls back
to the ratio of the actual pulled-back sections. The scalar equation and
unit-denominator cancellation identify it with the canonical Proj evaluation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open Scheme.Modules
namespace FLT.Mazur.SectionGradedChartEvaluation
open FCurve ModuleLineBundleTensorPullback SectionGradedMultiplication SectionGradedSum
open SectionGradedChartComparison SectionGradedPowerGenerators SectionGradedCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme} (L : X.Modules) [hL : Fact (LocallyFreeRankOne L)]
  (p : Y ⟶ X) [IsOpenImmersion p]
  (e : (pullback p).obj L ≅ structureModule Y)
  (d : ℕ) (s : Piece L ⊤ d)
  (hp : p ''ᵁ ⊤ ≤ sectionGeneratorOpen (tensorPower L d) s)
  (hs : IsUnit (SectionGradedProjChart.ringHom p L e (of L ⊤ d s)))

/-- Open pullback of the intrinsic comparison is the canonical local Proj evaluation. -/
lemma toFunctions_evaluation :
    (p.appIso ⊤).hom.hom.comp (toFunctions L d s (p ''ᵁ ⊤) hp) =
      SectionGradedProjChart.evaluation p L e (of L ⊤ d s) hs := by
  ext z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (grade L ⊤)
    (show of L ⊤ d s ∈ grade L ⊤ d from ⟨s, rfl⟩) z
  have ha' : a ∈ grade L ⊤ (d * n) := by
    simpa only [nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] using ha
  obtain ⟨t, rfl⟩ := ha'
  rw [RingHom.comp_apply, SectionGradedChartRatios.toFunctions_eq_coefficient]
  have hu : IsUnit (SectionGradedProjChart.ringHom p L e
      (of L ⊤ (d * n) (powerSection L d s n))) := by
    rw [of_powerSection, map_pow]
    exact hs.pow n
  have := SectionGradedProjChart.pullGenerator_isIso_of_ringHom p L e (powerSection L d s n) hu
  change (p.appIso ⊤).hom
      (sectionRatioOn (tensorPower L (d * n)) (powerSection L d s n) (p ''ᵁ ⊤)
        (hp.trans (le_generatorOpen_powerSection L hL.out d s n)) t) = _
  rw [sectionRatioOn_openPullback]
  apply (hs.pow n).mul_left_inj.mp
  have he := sectionRatio_smul ((pullback p).obj (tensorPower L (d * n)))
    (pullGlobal p _ (powerSection L d s n)) (pullGlobal p _ t)
  have hc := congrArg ((tensorPowerIso p L (d * n)).hom.app ⊤) he
  rw [Hom.app_smul] at hc
  have hd := (SectionGradedCoordinateEvaluation.coordinate_equation_iff e ⊤ (d * n) _ _ _).mpr hc
  have hd' : sectionRatio ((pullback p).obj (tensorPower L (d * n)))
      (pullGlobal p _ (powerSection L d s n)) (pullGlobal p _ t) *
      SectionGradedProjChart.ringHom p L e (of L ⊤ (d * n) (powerSection L d s n)) =
      SectionGradedProjChart.ringHom p L e (of L ⊤ (d * n) t) := by
    rw [SectionGradedProjChart.ringHom_of, SectionGradedProjChart.ringHom_of]
    exact hd
  rw [of_powerSection, map_pow] at hd'
  have hv := GradedProjUnitChart.evaluation_mk_mul (grade L ⊤)
    (SectionGradedProjChart.ringHom p L e) (of L ⊤ d s) hs
    ⟨n • d, ⟨of L ⊤ (d * n) t, ha⟩,
      ⟨(of L ⊤ d s) ^ n, SetLike.pow_mem_graded n ⟨s, rfl⟩⟩, ⟨n, rfl⟩⟩
  change SectionGradedProjChart.evaluation p L e (of L ⊤ d s) hs
    (Away.mk (grade L ⊤) ⟨s, rfl⟩ n (of L ⊤ (d * n) t) ha) *
      SectionGradedProjChart.ringHom p L e ((of L ⊤ d s) ^ n) = _ at hv
  rw [map_pow] at hv
  exact hd'.trans hv.symm

end FLT.Mazur.SectionGradedChartEvaluation
