/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MinimalPrimeLocalizedIdeal
public import FLT.Mazur.AffineBoundaryTestPowerEquations

/-!
# Boundary equations on full generic local coefficient rings

Localize the actual finite test ideal at every minimal prime of the original
scalar product. The local ideals retain nilpotents. Their possibly different
nilpotence orders imply one global order recovering the full original product.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryProduct boundaryCoordinate
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T) (a : Finset B)
set_option quotPrecheck false
local notation "C" => Γ(boundaryProduct s κ, ⊤)
local instance genericTestPrime (Q : minimalPrimes C) : Q.val.IsPrime := Q.property.1.1

/-- The original test ideal in the entire local coefficient ring of a minimal component. -/
def boundaryGenericTestIdeal (Q : minimalPrimes C) : Ideal (Localization.AtPrime Q.val) :=
  (boundaryTestIdeal s κ a).map (algebraMap C (Localization.AtPrime Q.val))

/-- The local ideal is nilpotent exactly when the original tests vanish at that component. -/
theorem boundaryGenericTestIdeal_nilpotent_iff (Q : minimalPrimes C) :
    IsNilpotent (boundaryGenericTestIdeal s κ a Q) ↔
      ∀ t ∈ a, boundaryCoordinate s κ t ∈ Q.val := by
  rw [boundaryGenericTestIdeal,
    MinimalPrimeLocalizedIdeal.localized_nilpotent_iff _ (boundaryTestIdeal_fg s κ a),
    boundaryTestIdeal, Ideal.span_le]
  exact ⟨fun h t ht ↦ h ⟨t, ht, rfl⟩, fun h _ ⟨t, ht, he⟩ ↦ he ▸ h t ht⟩

/-- An actual failed test generates the unit ideal in the full generic local ring. -/
theorem boundaryGenericTestIdeal_eq_top (Q : minimalPrimes C) (t : B) (ht : t ∈ a)
    (hQ : boundaryCoordinate s κ t ∉ Q.val) : boundaryGenericTestIdeal s κ a Q = ⊤ := by
  exact MinimalPrimeLocalizedIdeal.localized_eq_top (boundaryTestIdeal s κ a) Q
    (fun h ↦ hQ (h (boundaryCoordinate_mem_testIdeal s κ a ht)))

/-- Each full local coefficient ring has a nilpotent or unit test ideal. -/
theorem boundaryGenericTestIdeal_nilpotent_or_top (Q : minimalPrimes C) :
    IsNilpotent (boundaryGenericTestIdeal s κ a Q) ∨ boundaryGenericTestIdeal s κ a Q = ⊤ :=
  MinimalPrimeLocalizedIdeal.localized_nilpotent_or_top _ (boundaryTestIdeal_fg s κ a) Q

/-- The generic local rings detect full-product nilpotence without any coefficient reduction. -/
theorem boundaryTestIdeal_nilpotent_iff_generic_local :
    IsNilpotent (boundaryTestIdeal s κ a) ↔
      ∀ Q : minimalPrimes C, IsNilpotent (boundaryGenericTestIdeal s κ a Q) :=
  MinimalPrimeLocalizedIdeal.nilpotent_iff_all_localized _ (boundaryTestIdeal_fg s κ a)

/-- Arbitrary componentwise local orders give a single equation on the unchanged full product. -/
theorem boundaryTestIdeal_power_of_generic_local_orders
    (h : ∀ Q : minimalPrimes C, ∃ k : ℕ, boundaryGenericTestIdeal s κ a Q ^ k = ⊥) :
    ∃ k : ℕ, boundaryTestIdeal s κ a ^ (k + 1) = ⊥ := by
  obtain ⟨k, hk⟩ := (boundaryTestIdeal_nilpotent_iff_generic_local s κ a).mpr h
  exact ⟨k, pow_eq_zero_of_le (Nat.le_succ k) hk⟩

/-- Those actual local equations recover a finite neighborhood as the entire original product. -/
theorem boundaryTest_recovery_of_generic_local_orders
    (h : ∀ Q : minimalPrimes C, ∃ k : ℕ, boundaryGenericTestIdeal s κ a Q ^ k = ⊥) :
    ∃ k : ℕ, IsIso (boundaryTestThickeningMap s κ a k) := by
  obtain ⟨k, hk⟩ := boundaryTestIdeal_power_of_generic_local_orders s κ a h
  exact ⟨k, (boundaryTestThickeningMap_isIso_iff s κ a k).mpr hk⟩

end FLT.Mazur.AffineScalarBoundaryNilpotence
