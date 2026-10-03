/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCharacterConstantBaseChange
public import FLT.GroupScheme.RaynaudCharacterDifferenceOperator

/-!
# Mixed character averages

Finite differences indexed by a list of characters compute mixed convolution
products. Their scalar constants commute with coefficient ring maps.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.CharacterAverage

variable {R S F V W : Type*} [CommRing R] [CommRing S] [Field F] [Fintype Fˣ]
  [Invertible (Fintype.card Fˣ : R)]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- Successive normalized differences with possibly different characters. -/
def mixed (cs : List (Fˣ →* Rˣ)) (f : F → V) : F → V :=
  match cs with
  | [] => f
  | χ :: cs => fun a ↦ ⅟(Fintype.card Fˣ : R) • ∑ u : Fˣ,
      (↑(χ u)⁻¹ : R) • (mixed cs f (a + u) - mixed cs f a)

/-- Linear maps commute with mixed differences. -/
theorem map_mixed (cs : List (Fˣ →* Rˣ)) (f : F → V) (g : V →ₗ[R] W) (a : F) :
    g (mixed cs f a) = mixed cs (fun b ↦ g (f b)) a := by
  induction cs generalizing a with
  | nil => rfl
  | cons χ cs ih => simp only [mixed, map_smul, map_sum, map_sub, ih]

/-- The scalar recursion is the bundled difference operator. -/
theorem mixed_cons (χ : Fˣ →* Rˣ) (cs : List (Fˣ →* Rˣ)) (f : F → R) :
    mixed (χ :: cs) f = step χ (mixed cs f) := rfl

/-- The mixed universal constant at a prescribed output character. -/
def mixedConstant (cs : List (Fˣ →* Rˣ)) (ψ : Fˣ →* Rˣ) : R :=
  mixed cs (value ψ) 0

variable [Invertible (Fintype.card Fˣ : S)]

/-- Mixed finite differences commute with coefficient ring maps. -/
theorem map_mixed_ring (f : R →+* S) (cs : List (Fˣ →* Rˣ)) (g : F → R) (a : F) :
    f (mixed cs g a) = mixed (cs.map (mapCharacter f)) (fun b ↦ f (g b)) a := by
  induction cs generalizing a with
  | nil => rfl
  | cons χ cs ih =>
    simp only [mixed, List.map_cons, smul_eq_mul, map_mul, map_sum, map_sub, ih]
    congr 1
    let : Invertible (f (Fintype.card Fˣ : R)) := Invertible.map f _
    simpa only [map_natCast] using map_invOf f (Fintype.card Fˣ : R)

/-- Mixed constants are functorial in their coefficient ring. -/
theorem map_mixedConstant (f : R →+* S) (cs : List (Fˣ →* Rˣ)) (ψ : Fˣ →* Rˣ) :
    f (mixedConstant cs ψ) =
      mixedConstant (cs.map (mapCharacter f)) (mapCharacter f ψ) := by
  simp only [mixedConstant, map_mixed_ring, map_value]

variable {A : Type*} [Ring A] [Algebra R A]

/-- Mixed scalar differences expand the product of reduced character averages. -/
theorem mixed_eq_prod_mul (cs : List (Fˣ →* Rˣ)) (s : F → A)
    (hadd : ∀ a b, s (a + b) = s a * s b) (a : F) :
    mixed cs s a = s a * (cs.map (fun χ : Fˣ →* Rˣ ↦
      ⅟(Fintype.card Fˣ : R) • ∑ u : Fˣ, (↑(χ u)⁻¹ : R) • (s u - 1))).prod := by
  induction cs generalizing a with
  | nil => simp [mixed]
  | cons χ cs ih =>
    simp only [mixed, ih, hadd, List.map_cons, List.prod_cons, mul_smul_comm,
      Finset.mul_sum, Finset.sum_mul, smul_mul_assoc, mul_sub, sub_mul, one_mul, mul_assoc]

end ThreeAdicPlan.CharacterAverage
