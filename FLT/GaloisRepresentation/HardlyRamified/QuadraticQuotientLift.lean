/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.IntegralCharacters
public import FLT.GaloisRepresentation.HardlyRamified.QuadraticCharacterLift

/-!
# The fixed rank-one lift of an actual quadratic quotient

The character is extracted from the residual representation and its surjective
quotient map. Its square-one condition is checked on that quotient action.
The sign lift then gives a continuous integral rank-one Galois representation.
No quotient of an arbitrary deformation is asserted to exist.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

open GaloisRepresentation

variable {k V : Type*} [Field k] [TopologicalSpace k] [DiscreteTopology k]
  [AddCommGroup V] [Module k V]
  (ρ : GaloisRep ℚ k V) (π : V →ₗ[k] k) (hπ : Function.Surjective π)
  (hstable : ∀ g, (LinearMap.ker π).map (ρ g) ≤ LinearMap.ker π)

/-- The character constructed from the actual rank-one residual quotient. -/
def residualQuotientCharacter : Field.absoluteGaloisGroup ℚ →* kˣ :=
  (exists_continuous_character_of_quotient ρ π hπ hstable).choose

/-- Continuity is inherited from the original representation. -/
theorem residualQuotientCharacter_continuous :
    Continuous (residualQuotientCharacter ρ π hπ hstable) :=
  (exists_continuous_character_of_quotient ρ π hπ hstable).choose_spec.1

/-- The extracted character describes the original quotient map. -/
theorem residualQuotientCharacter_action (g : Field.absoluteGaloisGroup ℚ) (v : V) :
    π (ρ g v) = (residualQuotientCharacter ρ π hπ hstable g : k) * π v :=
  (exists_continuous_character_of_quotient ρ π hπ hstable).choose_spec.2 g v

variable (hsquare : ∀ g v, π (ρ g (ρ g v)) = π v)

include hsquare in
/-- An involutive quotient action gives a quadratic extracted character. -/
theorem residualQuotientCharacter_sq (g : Field.absoluteGaloisGroup ℚ) :
    residualQuotientCharacter ρ π hπ hstable g ^ 2 = 1 := by
  obtain ⟨v, hv⟩ := hπ 1
  have h := hsquare g v
  rw [residualQuotientCharacter_action ρ π hπ hstable,
    residualQuotientCharacter_action ρ π hπ hstable, hv, mul_one] at h
  apply Units.ext
  simpa only [Units.val_pow_eq_pow_val, Units.val_one, pow_two, Units.val_mul] using h

variable (O : Type*) [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]

/-- The specified integral character, with no choice of a lift as input. -/
def fixedQuotientCharacter : Field.absoluteGaloisGroup ℚ →* Oˣ :=
  quadraticCharacterLift (residualQuotientCharacter ρ π hπ hstable)
    (residualQuotientCharacter_sq ρ π hπ hstable hsquare) O

omit [IsTopologicalRing O] in
/-- Its continuity follows from discrete residual coefficients. -/
theorem fixedQuotientCharacter_continuous :
    Continuous (fixedQuotientCharacter ρ π hπ hstable hsquare O) :=
  quadraticCharacterLift_continuous _ _ O
    (residualQuotientCharacter_continuous ρ π hπ hstable)

/-- The resulting rank-one integral Galois representation. -/
def fixedQuotientGaloisRep : GaloisRep ℚ O O :=
  characterGaloisRep (fixedQuotientCharacter ρ π hπ hstable hsquare O)
    (fixedQuotientCharacter_continuous ρ π hπ hstable hsquare O)

/-- Reduction of the integral action gives the action of the actual residual quotient. -/
theorem fixedQuotientGaloisRep_reduce (r : O →+* k)
    (g : Field.absoluteGaloisGroup ℚ) (a : O) :
    r (fixedQuotientGaloisRep ρ π hπ hstable hsquare O g a) =
      (residualQuotientCharacter ρ π hπ hstable g : k) * r a := by
  change r ((fixedQuotientCharacter ρ π hπ hstable hsquare O g : O) * a) = _
  rw [map_mul]
  congr 1
  exact congrArg Units.val (quadraticCharacterLift_reduce _ _ O r g)

/-- Trivial action on a subgroup is preserved by the constructed integral lift. -/
theorem fixedQuotientGaloisRep_trivial_on (N : Subgroup (Field.absoluteGaloisGroup ℚ))
    (hN : ∀ g ∈ N, ∀ v, π (ρ g v) = π v)
    (g : Field.absoluteGaloisGroup ℚ) (hg : g ∈ N) (a : O) :
    fixedQuotientGaloisRep ρ π hπ hstable hsquare O g a = a := by
  have hc : residualQuotientCharacter ρ π hπ hstable g = 1 := by
    obtain ⟨v, hv⟩ := hπ 1
    have h := hN g hg v
    rw [residualQuotientCharacter_action ρ π hπ hstable, hv, mul_one] at h
    exact Units.ext h
  have hl : fixedQuotientCharacter ρ π hπ hstable hsquare O g = 1 := by
    classical
    simp [fixedQuotientCharacter, quadraticCharacterLift, hc]
  change (fixedQuotientCharacter ρ π hπ hstable hsquare O g : O) * a = a
  rw [hl, Units.val_one, one_mul]

end ThreeAdicPlan
