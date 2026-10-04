/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedProjChart
public import FLT.Mazur.ModuleGlobalSectionPullback

/-!
# Naturality of the local section-ring Proj map

The scalar equation on pulled-back sections proves naturality without
choosing compatible tensor-power trivializations on different domains.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SectionGradedProjChart
open FCurve ModuleLineBundleTensorPullback SectionGradedSum
open SectionGradedCoordinateEvaluation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y Z : Scheme} (p : Y ⟶ X) (L : X.Modules) [Fact (LocallyFreeRankOne L)]
  (e : (pullback p).obj L ≅ structureModule Y)

/-- Chart evaluation solves the scalar equation in the pullback of the original tensor power. -/
lemma evaluation_mk_pullGlobal (f : SectionGradedSum.Sections L ⊤)
    (hf : IsUnit (ringHom p L e f))
    (c : HomogeneousLocalization.NumDenSameDeg (grade L ⊤) (Submonoid.powers f))
    (s t : SectionGradedMultiplication.Piece L ⊤ c.deg)
    (hs : of L ⊤ c.deg s = c.den) (ht : of L ⊤ c.deg t = c.num) :
    evaluation p L e f hf (HomogeneousLocalization.mk c) • pullGlobal p _ s =
      pullGlobal p _ t := by
  have he := GradedProjUnitChart.evaluation_mk_mul (grade L ⊤) (ringHom p L e) f hf c
  rw [← hs, ← ht, ringHom_of, ringHom_of] at he
  have he' := (coordinate_equation_iff e ⊤ c.deg _ _ _).mp he
  apply (ConcreteCategory.bijective_of_isIso ((tensorPowerIso p L c.deg).hom.app ⊤)).injective
  rw [Hom.app_smul]
  exact he'

/-- Homogeneous-fraction evaluation commutes with further pullback, in any line coordinates. -/
lemma evaluation_naturality (k : Z ⟶ Y)
    (e' : (pullback (k ≫ p)).obj L ≅ structureModule Z)
    (f : SectionGradedSum.Sections L ⊤)
    (hf : IsUnit (ringHom p L e f)) (hf' : IsUnit (ringHom (k ≫ p) L e' f)) :
    k.appTop.hom.comp (evaluation p L e f hf) = evaluation (k ≫ p) L e' f hf' := by
  ext z
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  obtain ⟨s, hs⟩ := c.den.property
  obtain ⟨t, ht⟩ := c.num.property
  have he := congrArg (pullGlobal k ((pullback p).obj (tensorPower L c.deg)))
    (evaluation_mk_pullGlobal p L e f hf c s t hs ht)
  rw [map_smulₛₗ] at he
  have hc := congrArg (((pullbackComp k p).hom.app (tensorPower L c.deg)).app ⊤) he
  rw [Hom.app_smul, pullGlobal_comp_hom, pullGlobal_comp_hom] at hc
  have hd := congrArg ((tensorPowerIso (k ≫ p) L c.deg).hom.app ⊤) hc
  rw [Hom.app_smul] at hd
  have hcoord := (coordinate_equation_iff e' ⊤ c.deg _ _ _).mpr hd
  apply (GradedProjUnitChart.denominator_isUnit
    (grade L ⊤) (ringHom (k ≫ p) L e') f hf' c).mul_left_inj.mp
  unfold evaluation
  rw [GradedProjUnitChart.evaluation_mk_mul]
  rw [← hs, ← ht, ringHom_of, ringHom_of]
  exact hcoord

/-- The actual local Proj map commutes with further pullback, independently of coordinates. -/
lemma toProj_naturality (k : Z ⟶ Y)
    (e' : (pullback (k ≫ p)).obj L ≅ structureModule Z)
    (f : SectionGradedSum.Sections L ⊤)
    (hf : IsUnit (ringHom p L e f)) (hf' : IsUnit (ringHom (k ≫ p) L e' f))
    {d : ℕ} (hd : f ∈ grade L ⊤ d) (hpos : 0 < d) :
    k ≫ toProj p L e f hf hd hpos = toProj (k ≫ p) L e' f hf' hd hpos := by
  unfold toProj GradedProjUnitChart.toProj GradedProjUnitChart.toAffine
  simp only [← Category.assoc, Scheme.toSpecΓ_naturality]
  simp only [Category.assoc, ← Spec.map_comp]
  congr 3
  exact CommRingCat.hom_ext (evaluation_naturality p L e k e' f hf hf')

end FLT.Mazur.SectionGradedProjChart
