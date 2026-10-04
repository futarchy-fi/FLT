/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjUnitChart
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Unit-coordinate charts and graded ring maps

Evaluation of homogeneous fractions commutes with graded ring maps. Hence
local maps into Proj are compatible with the induced Proj morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry HomogeneousLocalization HomogeneousIdeal
universe u
namespace FLT.Mazur.GradedProjUnitChartMap
variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (φ : 𝒜 →+*ᵍ ℬ) {X : Scheme.{u}} (ψ : B →+* Γ(X, ⊤))
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Evaluation after a graded localization map evaluates the mapped numerator and denominator. -/
lemma evaluation_map (f : A) (hf : IsUnit (ψ (φ f))) :
    (GradedProjUnitChart.evaluation ℬ ψ (φ f) hf).comp (Away.map φ f) =
      GradedProjUnitChart.evaluation 𝒜 (ψ.comp φ.toRingHom) f hf := by
  ext z
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  apply (GradedProjUnitChart.denominator_isUnit 𝒜 (ψ.comp φ.toRingHom) f hf c).mul_left_inj.mp
  rw [GradedProjUnitChart.evaluation_mk_mul]
  change GradedProjUnitChart.evaluation ℬ ψ (φ f) hf
    (HomogeneousLocalization.map φ _ (HomogeneousLocalization.mk c)) * ψ (φ c.den) =
      ψ (φ c.num)
  rw [HomogeneousLocalization.map_mk]
  exact GradedProjUnitChart.evaluation_mk_mul ℬ ψ (φ f) hf _

/-- Affine homogeneous charts commute with graded ring maps. -/
@[reassoc]
lemma toAffine_map (f : A) (hf : IsUnit (ψ (φ f))) :
    GradedProjUnitChart.toAffine ℬ ψ (φ f) hf ≫
      Spec.map (CommRingCat.ofHom (Away.map φ f)) =
        GradedProjUnitChart.toAffine 𝒜 (ψ.comp φ.toRingHom) f hf := by
  simp only [GradedProjUnitChart.toAffine, Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, evaluation_map]

/-- A local unit-coordinate Proj morphism is natural in the graded ring. -/
@[reassoc]
lemma toProj_map (hφ : ℬ₊ ≤ 𝒜₊.map φ) {d : ℕ} (f : A) (hd : f ∈ 𝒜 d)
    (hpos : 0 < d) (hf : IsUnit (ψ (φ f))) :
    GradedProjUnitChart.toProj ℬ ψ (φ f) hf (φ.map_mem hd) hpos ≫ Proj.map φ hφ =
      GradedProjUnitChart.toProj 𝒜 (ψ.comp φ.toRingHom) f hf hd hpos := by
  rw [GradedProjUnitChart.toProj, Category.assoc,
    Proj.awayι_comp_map φ hφ hpos f hd, ← Category.assoc, toAffine_map]
  rfl

end FLT.Mazur.GradedProjUnitChartMap
