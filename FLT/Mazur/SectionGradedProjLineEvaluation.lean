/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedProjPullbackEvaluation
public import FLT.Mazur.SectionGradedLineGeneratorOpen
public import FLT.Mazur.GradedProjUnitChartMap

/-!
# Homogeneous fractions for a specified line pullback comparison

The two evaluations agree by transporting the numerator-denominator equation
through tensor-power pullback and cancelling the invertible denominator.
No compatibility of the chosen line coordinates is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open Scheme.Modules
namespace FLT.Mazur.SectionGradedProjLineEvaluation
open FCurve ModuleLineBundleTensorPullback SectionGradedSum
open SectionGradedCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y Z : Scheme} (p : Y ⟶ X) (k : Z ⟶ Y) (L : X.Modules)
  {M : Y.Modules} (eL : (pullback p).obj L ≅ M)

/-- Scalar equations descend through the specified tensor-line comparison. -/
lemma scalar_equation_comp (n : ℕ) (s t : Γ(tensorPower L n, ⊤)) (a : Γ(Z, ⊤))
    (he : a • pullGlobal k (tensorPower M n)
        (SectionGradedLinePullback.sectionMap p eL n ⊤ s) =
      pullGlobal k (tensorPower M n)
        (SectionGradedLinePullback.sectionMap p eL n ⊤ t)) :
    a • pullGlobal (k ≫ p) (tensorPower L n) s =
      pullGlobal (k ≫ p) (tensorPower L n) t := by
  apply SectionGradedProjPullbackEvaluation.scalar_equation_comp p k L n s t a
  apply (ConcreteCategory.bijective_of_isIso
    (((pullback k).map (tensorPowerCongr eL n).hom).app ⊤)).injective
  rw [Hom.app_smul, pullGlobal_naturality, pullGlobal_naturality]
  exact he

/-- The specified comparison also defines the full graded ring pullback. -/
def gradedRingHom : grade L ⊤ →+*ᵍ grade M ⊤ :=
  (SectionGradedIso.gradedRingHom eL ⊤).comp (SectionGradedPullback.gradedRingHom p L)

variable [hL : Fact (LocallyFreeRankOne L)]

variable [Fact (LocallyFreeRankOne M)]

/-- Evaluating a pulled homogeneous fraction agrees with evaluation on the composite domain. -/
lemma evaluation_map
    (e : (pullback k).obj M ≅ structureModule Z)
    (e' : (pullback (k ≫ p)).obj L ≅ structureModule Z)
    (f : SectionGradedSum.Sections L ⊤)
    (hf : IsUnit (SectionGradedProjChart.ringHom k M e
      (SectionGradedLinePullback.ringHom p eL f)))
    (hf' : IsUnit (SectionGradedProjChart.ringHom (k ≫ p) L e' f)) :
    (SectionGradedProjChart.evaluation k M e
      (SectionGradedLinePullback.ringHom p eL f) hf).comp
        (Away.map (gradedRingHom p L eL) f) =
      SectionGradedProjChart.evaluation (k ≫ p) L e' f hf' := by
  ext z
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  obtain ⟨s, hs⟩ := c.den.property
  obtain ⟨t, ht⟩ := c.num.property
  let φ := gradedRingHom p L eL
  have hw : Submonoid.powers f ≤ (Submonoid.powers (φ f)).comap φ := by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, by simp⟩
  let c' := c.map φ hw
  have hs' : of M ⊤ c'.deg
      (SectionGradedLinePullback.sectionMap p eL c.deg ⊤ s) = c'.den := by
    change _ = SectionGradedLinePullback.ringHom p eL c.den
    rw [← hs]
    exact (SectionGradedLinePullback.ringHom_of p eL c.deg s).symm
  have ht' : of M ⊤ c'.deg
      (SectionGradedLinePullback.sectionMap p eL c.deg ⊤ t) = c'.num := by
    change _ = SectionGradedLinePullback.ringHom p eL c.num
    rw [← ht]
    exact (SectionGradedLinePullback.ringHom_of p eL c.deg t).symm
  have he := SectionGradedProjChart.evaluation_mk_pullGlobal k M e
    (φ f) hf c' _ _ hs' ht'
  have hb := scalar_equation_comp p k L eL c.deg s t _ he
  have hc := congrArg ((tensorPowerIso (k ≫ p) L c.deg).hom.app ⊤) hb
  rw [Hom.app_smul] at hc
  have hd := (SectionGradedCoordinateEvaluation.coordinate_equation_iff
    e' ⊤ c.deg _ _ _).mpr hc
  apply (GradedProjUnitChart.denominator_isUnit
    (grade L ⊤) (SectionGradedProjChart.ringHom (k ≫ p) L e') f hf' c).mul_left_inj.mp
  change SectionGradedProjChart.evaluation k M e (φ f) hf
    (HomogeneousLocalization.mk c') * SectionGradedProjChart.ringHom (k ≫ p) L e' c.den =
      GradedProjUnitChart.evaluation (grade L ⊤)
        (SectionGradedProjChart.ringHom (k ≫ p) L e') f hf'
          (HomogeneousLocalization.mk c) * SectionGradedProjChart.ringHom (k ≫ p) L e' c.den
  rw [GradedProjUnitChart.evaluation_mk_mul]
  rw [← hs, ← ht, SectionGradedProjChart.ringHom_of, SectionGradedProjChart.ringHom_of]
  exact hd

omit hL [Fact (LocallyFreeRankOne M)] in
/-- Generating sections persist under the specified pulled line comparison. -/
lemma ringHom_isUnit_pull_section
    (e : (pullback k).obj M ≅ structureModule Z)
    (e' : (pullback (k ≫ p)).obj L ≅ structureModule Z)
    {d : ℕ} (s : Γ(tensorPower L d, ⊤))
    (hs : IsUnit (SectionGradedProjChart.ringHom (k ≫ p) L e' (of L ⊤ d s))) :
    IsUnit (SectionGradedProjChart.ringHom k M e
      (of M ⊤ d (SectionGradedLinePullback.sectionMap p eL d ⊤ s))) := by
  let ep := (pullback k).mapIso eL ≪≫ e
  have hu := SectionGradedProjPullbackEvaluation.ringHom_isUnit_pull_section
    p k L ep e' s hs
  have := SectionGradedProjChart.pullGenerator_isIso_of_ringHom k
    ((pullback p).obj L) ep (SectionGradedPullback.pull p L d ⊤ s) hu
  have hi := globalSectionHom_isIso_transport _
    ((pullback k).mapIso (tensorPowerCongr eL d))
      (pullGlobal k _ (SectionGradedPullback.pull p L d ⊤ s))
  change IsIso (globalSectionHom _
    (((pullback k).map (tensorPowerCongr eL d).hom).app ⊤
      (pullGlobal k _ (SectionGradedPullback.pull p L d ⊤ s)))) at hi
  rw [pullGlobal_naturality] at hi
  have : IsIso (globalSectionHom _
      (pullGlobal k _ (SectionGradedLinePullback.sectionMap p eL d ⊤ s))) := hi
  exact SectionGradedProjChart.ringHom_isUnit_of_pullGenerator k M e _

/-- Local canonical maps commute with a globally defined section-ring Proj pullback. -/
@[reassoc]
lemma toProj_map
    (e : (pullback k).obj M ≅ structureModule Z)
    (e' : (pullback (k ≫ p)).obj L ≅ structureModule Z)
    (hφ : HomogeneousIdeal.irrelevant (grade M ⊤) ≤
      (HomogeneousIdeal.irrelevant (grade L ⊤)).map
        (gradedRingHom p L eL))
    {d : ℕ} (s : Γ(tensorPower L d, ⊤)) (hd : 0 < d)
    (hs : IsUnit (SectionGradedProjChart.ringHom k M e
      (SectionGradedLinePullback.ringHom p eL (of L ⊤ d s))))
    (hs' : IsUnit (SectionGradedProjChart.ringHom (k ≫ p) L e' (of L ⊤ d s))) :
    SectionGradedProjChart.toProj k M e
      (SectionGradedLinePullback.ringHom p eL (of L ⊤ d s)) hs
      ((gradedRingHom p L eL).map_mem ⟨s, rfl⟩) hd ≫
        Proj.map (gradedRingHom p L eL) hφ =
      SectionGradedProjChart.toProj (k ≫ p) L e' (of L ⊤ d s) hs' ⟨s, rfl⟩ hd := by
  unfold SectionGradedProjChart.toProj GradedProjUnitChart.toProj
  rw [Category.assoc]
  erw [Proj.awayι_comp_map _ hφ hd _ ⟨s, rfl⟩]
  rw [← Category.assoc]
  congr 1
  unfold GradedProjUnitChart.toAffine
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun v ↦ Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom v))
    (evaluation_map p k L eL e e' _ hs hs')

end FLT.Mazur.SectionGradedProjLineEvaluation
