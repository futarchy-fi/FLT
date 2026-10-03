/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudUniversalCharacterConstant

/-!
# Changing the coefficient ring of universal constants

The explicit finite differences commute with ring homomorphisms. In
particular their images in residue and quotient rings can be calculated
there, using the transported characters.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.CharacterAverage

variable {R S F : Type*} [CommRing R] [CommRing S] [Field F]
  (f : R →+* S)

/-- Transport a character along a coefficient ring homomorphism. -/
def mapCharacter (χ : Fˣ →* Rˣ) : Fˣ →* Sˣ := (Units.map f.toMonoidHom).comp χ

/-- Extension by zero commutes with a change of coefficient ring. -/
theorem map_value (χ : Fˣ →* Rˣ) (a : F) :
    f (value χ a) = value (mapCharacter f χ) a := by
  classical
  by_cases ha : a = 0
  · simp [ha]
  · simp [value, ha, mapCharacter]

variable [Fintype Fˣ] [Invertible (Fintype.card Fˣ : R)]
  [Invertible (Fintype.card Fˣ : S)]

/-- The normalized finite-difference recursion commutes with ring homomorphisms. -/
theorem map_iterate_ring (χ : Fˣ →* Rˣ) (g : F → R) (n : ℕ) (a : F) :
    f (iterate χ g n a) = iterate (mapCharacter f χ) (fun b ↦ f (g b)) n a := by
  induction n generalizing a with
  | zero => rfl
  | succ n hn =>
    simp only [iterate, smul_eq_mul, map_mul, map_sum, map_sub, hn]
    congr 1
    let : Invertible (f (Fintype.card Fˣ : R)) := Invertible.map f _
    simpa only [map_natCast] using map_invOf f (Fintype.card Fˣ : R)

/-- Universal constants are functorial in their coefficient ring. -/
theorem map_constant (χ ψ : Fˣ →* Rˣ) (n : ℕ) :
    f (constant χ ψ n) = constant (mapCharacter f χ) (mapCharacter f ψ) n := by
  simp only [constant, map_iterate_ring, map_value]

end ThreeAdicPlan.CharacterAverage
