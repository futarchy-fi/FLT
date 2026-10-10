/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFamilySupportOpen

/-!
# Arbitrary base change of finite-family support opens

Images of complements commute with actual scheme pullbacks. Consequently the
support open commutes with every base change, and a test base maps into it
exactly when its entire actual pulled-back family lies in the prescribed open.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve

variable {D E S T : Scheme.{u}} (p : D ⟶ S) [IsFinite p] (U : D.Opens)
variable (q : E ⟶ D) (r : E ⟶ T) (g : T ⟶ S) (h : IsPullback q r p g)

include h in
/-- Support opens of actual finite families commute with arbitrary cartesian base change. -/
theorem finiteFamilySupportOpen_baseChange [IsFinite r] :
    finiteFamilySupportOpen r (q ⁻¹ᵁ U) = g ⁻¹ᵁ finiteFamilySupportOpen p U := by
  apply TopologicalSpace.Opens.coe_inj.mp
  change (r '' (q ⁻¹' (U : Set D))ᶜ)ᶜ = g ⁻¹' (p '' (U : Set D)ᶜ)ᶜ
  rw [← Set.preimage_compl]
  have he := Scheme.image_preimage_eq_of_isPullback h (U : Set D)ᶜ
  change r '' q ⁻¹' (U : Set D)ᶜ = g ⁻¹' p '' (U : Set D)ᶜ at he
  rw [he]
  rfl

include h in
/-- A test base maps into the support open iff its whole actual pullback family maps into U. -/
theorem range_subset_finiteFamilySupportOpen_iff :
    Set.range g ⊆ finiteFamilySupportOpen p U ↔ Set.range q ⊆ U := by
  constructor
  · rintro hg _ ⟨z, rfl⟩
    apply (mem_finiteFamilySupportOpen p U (g (r z))).mp (hg ⟨r z, rfl⟩) (q z)
    exact congrArg (fun a ↦ a z) h.w
  · rintro hq _ ⟨t, rfl⟩
    apply (mem_finiteFamilySupportOpen p U (g t)).mpr
    intro x hx
    obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback h x t hx
    exact hq ⟨z, hz⟩

/-- A morphism factors through an actual open subscheme exactly when its range lies in the open. -/
theorem factors_open_iff {A B : Scheme.{u}} (a : A ⟶ B) (V : B.Opens) :
    (∃ b : A ⟶ V.toScheme, b ≫ V.ι = a) ↔ Set.range a ⊆ V := by
  constructor
  · rintro ⟨b, rfl⟩ _ ⟨x, rfl⟩
    exact (b x).property
  · intro ha
    have hb : Set.range a ⊆ Set.range V.ι := by simpa only [Scheme.Opens.range_ι] using ha
    exact ⟨IsOpenImmersion.lift V.ι a hb, IsOpenImmersion.lift_fac _ _ _⟩

include h in
/-- The support open represents exact open factorization of the actual base-changed family. -/
theorem finiteFamilySupportOpen_factorization_iff :
    (∃ a : T ⟶ (finiteFamilySupportOpen p U).toScheme,
      a ≫ (finiteFamilySupportOpen p U).ι = g) ↔
      ∃ b : E ⟶ U.toScheme, b ≫ U.ι = q := by
  rw [factors_open_iff, factors_open_iff]
  exact range_subset_finiteFamilySupportOpen_iff p U q r g h

end FLT.Mazur.FCurve
