/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjUnitChart

/-!
# Inverse images of basic opens under unit-coordinate charts

A positive homogeneous element pulls back to the basic open of its evaluated
coordinate. The proof uses its power divided by the chosen unit denominator.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
universe u
namespace FLT.Mazur.GradedProjUnitChartOpens
variable {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme.{u}} (φ : A →+* Γ(X, ⊤))
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The standard localization element evaluates to the expected ratio of powers. -/
lemma evaluation_localizationElem {f g : A} {d n : ℕ} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 n)
    (hu : IsUnit (φ f)) :
    GradedProjUnitChart.evaluation 𝒜 φ f hu (Away.isLocalizationElem hf hg) * φ f ^ n =
      φ g ^ d := by
  unfold Away.isLocalizationElem Away.mk
  rw [← map_pow, ← map_pow]
  exact GradedProjUnitChart.evaluation_mk_mul 𝒜 φ f hu _


/-- Every positive Proj basic open pulls back to its evaluated basic open. -/
lemma toProj_preimage_basicOpen {f g : A} {d n : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (hg : g ∈ 𝒜 n) (hn : 0 < n) (hu : IsUnit (φ f)) :
    GradedProjUnitChart.toProj 𝒜 φ f hu hf hd ⁻¹ᵁ Proj.basicOpen 𝒜 g =
      X.basicOpen (φ g) := by
  rw [GradedProjUnitChart.toProj, Scheme.Hom.comp_preimage]
  rw [Proj.awayι_preimage_basicOpen (𝒜 := 𝒜) hf hd hg hn]
  change X.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen
    (GradedProjUnitChart.evaluation 𝒜 φ f hu (Away.isLocalizationElem hf hg)) = _
  rw [Scheme.toSpecΓ_preimage_basicOpen]
  have he := congrArg (fun a : Γ(X, ⊤) ↦ X.basicOpen a)
    (evaluation_localizationElem 𝒜 φ hf hg hu)
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (hu.pow n), inf_top_eq,
    Scheme.basicOpen_pow _ _ hd] at he
  exact he

end FLT.Mazur.GradedProjUnitChartOpens
