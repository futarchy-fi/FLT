/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexGaloisAction

/-! # Relative automorphisms of the actual algebraic p-adic closure -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime] (E : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- The original algebraic closure is integral over every actual intermediate field. -/
instance instIntegralPadicIntermediateField : Algebra.IsIntegral E (PadicAlgCl p) :=
  ⟨fun x ↦ (Algebra.IsIntegral.isIntegral (R := ℚ_[p]) x).tower_top⟩

/-- Every relative automorphism preserves the original p-adic norm. -/
theorem padicRelativeGalois_isometry (σ : Gal(PadicAlgCl p/E)) : Isometry σ :=
  padicGalois_isometry p (σ.restrictScalars ℚ_[p])

/-- Moving to a nearby algebraic point transfers a relative displacement bound. -/
theorem padicRelativeGalois_displacement_nearby (a b : PadicAlgCl p) {r d : ℝ}
    (ha : ∀ σ : Gal(PadicAlgCl p/E), ‖σ a - a‖ ≤ r) (hab : ‖a - b‖ ≤ d) :
    ∀ σ : Gal(PadicAlgCl p/E), ‖σ b - b‖ ≤ max r d := by
  intro σ
  have he : σ b - b = σ (b - a) + (σ a - a) + (a - b) := by rw [map_sub]; ring
  have hn : ‖σ (b - a)‖ = ‖a - b‖ := by
    rw [(padicRelativeGalois_isometry p E σ).norm_map_of_map_zero (map_zero _) _, norm_sub_rev]
  rw [he]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  apply max_le
  · apply (IsUltrametricDist.norm_add_le_max _ _).trans
    rw [hn]
    exact max_le (hab.trans (le_max_right _ _)) ((ha σ).trans (le_max_left _ _))
  · exact hab.trans (le_max_right _ _)

end PadicHodgeTheory
