/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjMapChartSections

/-!
# Fraction evaluation after a graded Proj map

A further scheme pullback evaluates the specified image fraction on the
specified target chart. This separates chart composition from section rings.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

namespace FLT.Mazur.GradedProjMapPullbackSections

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] Proj.map Proj.awayToSection
  GradedProjMapChartSections.fractionMap

variable {A B : Type} [CommRing A] [CommRing B]
  {σ τ : Type} [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (φ : 𝒜 →+*ᵍ ℬ)
  (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)
  (s : A) (t : B) (ht : φ s = t)
  {X : Scheme} (p : X ⟶ Proj ℬ) (U : X.Opens)
  (hU : U ≤ p ⁻¹ᵁ Proj.basicOpen ℬ t)

include ht hU in
/-- The chosen chart lies above the source denominator under the composite. -/
theorem le_preimage : U ≤ (p ≫ Proj.map φ hφ) ⁻¹ᵁ Proj.basicOpen 𝒜 s := by
  rw [Scheme.Hom.comp_preimage, Proj.map_preimage_basicOpen, ht]
  exact hU

/-- Evaluating the composite morphism is evaluating the specified image fraction. -/
theorem fraction_evaluation {d : ℕ} (hs : s ∈ 𝒜 d) (z : Away 𝒜 s) :
    (p ≫ Proj.map φ hφ).appLE (Proj.basicOpen 𝒜 s) U
        (le_preimage 𝒜 ℬ φ hφ s t ht p U hU) (Proj.awayToSection 𝒜 s z) =
      p.appLE (Proj.basicOpen ℬ t) U hU
        (Proj.awayToSection ℬ t
          (GradedProjMapChartSections.fractionMap 𝒜 ℬ φ s t ht z)) := by
  have he := congrArg (fun g ↦ g ≫ p.appLE (Proj.basicOpen ℬ t) U hU)
    (GradedProjMapChartSections.awayToSection_appLE 𝒜 ℬ φ s t ht hφ hs)
  rw [Category.assoc, Scheme.Hom.appLE_comp_appLE] at he
  exact ConcreteCategory.congr_hom he z

end FLT.Mazur.GradedProjMapPullbackSections
