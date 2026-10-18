/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBoundaryTestThickenings

/-!
# Exact factorization through a finite boundary test neighborhood

Nilpotence of the pulled-back finite test ideal constructs a scheme morphism
through some ideal-power neighborhood. The factorization is unique over the
original full product. This retains all coefficients of the supplied scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryProduct boundaryCoordinate
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T) (a : Finset B)
  {Y : Scheme.{0}} (v : Y ⟶ boundaryProduct s κ)

/-- Nilpotence constructs an actual finite-order kernel inclusion on the full scalar product. -/
theorem exists_boundaryTestSheaf_pow_le_kernel
    (h : IsNilpotent ((boundaryTestIdeal s κ a).map v.appTop.hom)) :
    ∃ k : ℕ, boundaryTestSheaf s κ a ^ (k + 1) ≤ v.ker := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  apply Scheme.IdealSheafData.le_of_isAffine
  rw [Scheme.ker_of_isAffine]
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, boundaryTestSheaf,
    Scheme.IdealSheafData.ofIdealTop_ideal]
  simp only [homOfLE_refl, op_id]
  rw [(boundaryProduct s κ).presheaf.map_id]
  simp only [CommRingCat.hom_id, Ideal.map_id]
  apply (Ideal.map_eq_bot_iff_le_ker v.appTop.hom).mp
  rw [Ideal.map_pow, pow_succ, hk, zero_mul]
  rfl

/-- The unchanged coefficient scheme factors through an actual ideal-power neighborhood. -/
theorem exists_boundaryTestThickening_factor
    (h : IsNilpotent ((boundaryTestIdeal s κ a).map v.appTop.hom)) :
    ∃ (k : ℕ) (w : Y ⟶ boundaryTestThickening s κ a k),
      w ≫ boundaryTestThickeningMap s κ a k = v := by
  obtain ⟨k, hk⟩ := exists_boundaryTestSheaf_pow_le_kernel s κ a v h
  refine ⟨k, v.toImage ≫ Scheme.IdealSheafData.inclusion hk, ?_⟩
  change (v.toImage ≫ Scheme.IdealSheafData.inclusion hk) ≫
    (boundaryTestSheaf s κ a ^ (k + 1)).subschemeι = v
  rw [Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι, v.toImage_imageι]

/-- The finite-order factor is unique as a morphism over the original product. -/
theorem boundaryTestThickening_factor_unique (k : ℕ)
    (w₁ w₂ : Y ⟶ boundaryTestThickening s κ a k)
    (h₁ : w₁ ≫ boundaryTestThickeningMap s κ a k = v)
    (h₂ : w₂ ≫ boundaryTestThickeningMap s κ a k = v) : w₁ = w₂ := by
  apply (cancel_mono (boundaryTestThickeningMap s κ a k)).mp
  exact h₁.trans h₂.symm

/-- Nilpotence recovers the entire unreduced product at a finite order, as an isomorphism. -/
theorem exists_boundaryTestThickening_isIso
    (h : IsNilpotent (boundaryTestIdeal s κ a)) :
    ∃ k : ℕ, IsIso (boundaryTestThickeningMap s κ a k) := by
  have hi : IsNilpotent ((boundaryTestIdeal s κ a).map
      (𝟙 (boundaryProduct s κ) : boundaryProduct s κ ⟶ boundaryProduct s κ).appTop.hom) := by
    simpa only [Scheme.Hom.id_appTop, CommRingCat.hom_id, Ideal.map_id] using h
  obtain ⟨k, w, hw⟩ := exists_boundaryTestThickening_factor s κ a (𝟙 _) hi
  refine ⟨k, ⟨w, ?_, hw⟩⟩
  apply (cancel_mono (boundaryTestThickeningMap s κ a k)).mp
  rw [Category.assoc, hw, Category.comp_id, Category.id_comp]

end FLT.Mazur.AffineScalarBoundaryNilpotence
