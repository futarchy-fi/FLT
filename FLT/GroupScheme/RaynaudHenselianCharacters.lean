/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.NumberTheory.MulChar.Duality

/-!
# Characters over the strict Henselian base

Simple roots of unity lift from the residue field. A lift of a primitive
root remains primitive, providing enough integral roots of unity for the
finite scalar group and hence a complete separating character system.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open Polynomial IsLocalRing

variable {R : Type*} [CommRing R] [HenselianLocalRing R]

/-- Lift a prescribed prime-to-residue-characteristic root of unity. -/
theorem henselian_lift_rootOfUnity {n : ℕ} (hn : (n : ResidueField R) ≠ 0)
    (ζ : ResidueField R) (hζ : ζ ^ n = 1) :
    ∃ z : R, z ^ n = 1 ∧ residue R z = ζ := by
  have hn0 : n ≠ 0 := by intro h; simp [h] at hn
  have hz0 : ζ ≠ 0 := by intro h; simp [h, hn0] at hζ
  have H := ((HenselianLocalRing.TFAE R).out 1 2).mp (inferInstance : HenselianLocalRing R)
  obtain ⟨z, hz, he⟩ := H (X ^ n - 1) (monic_X_pow_sub_C 1 hn0) ζ
    (by simpa using sub_eq_zero.mpr hζ) (by
      simpa [derivative_pow, hn0] using mul_ne_zero hn (pow_ne_zero (n - 1) hz0))
  exact ⟨z, by simpa [IsRoot, sub_eq_zero] using hz, he⟩

/-- A lift of a primitive residue root is primitive over the base ring. -/
theorem henselian_lift_primitiveRoot {n : ℕ} (hn : (n : ResidueField R) ≠ 0)
    (ζ : ResidueField R) (hζ : IsPrimitiveRoot ζ n) :
    ∃ z : R, IsPrimitiveRoot z n ∧ residue R z = ζ := by
  obtain ⟨z, hz, he⟩ := henselian_lift_rootOfUnity hn ζ hζ.pow_eq_one
  refine ⟨z, ⟨hz, fun k hk ↦ hζ.dvd_of_pow_eq_one k ?_⟩, he⟩
  simpa [he] using congrArg (residue R) hk

/-- The strict Henselian domain has enough roots of every invertible order. -/
theorem henselian_hasEnoughRootsOfUnity [IsDomain R] [IsSepClosed (ResidueField R)]
    (n : ℕ) (hn : (n : ResidueField R) ≠ 0) : HasEnoughRootsOfUnity R n := by
  let : NeZero (n : ResidueField R) := ⟨hn⟩
  have : NeZero n := .of_neZero_natCast (ResidueField R)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (ResidueField R) n
  obtain ⟨z, hz, _⟩ := henselian_lift_primitiveRoot hn ζ hζ
  exact ⟨⟨z, hz⟩, rootsOfUnity.isCyclic R n⟩

/-- Integral character duality for a finite abelian group of invertible order. -/
theorem henselian_group_characters [IsDomain R] [IsSepClosed (ResidueField R)]
    (G : Type*) [CommGroup G] [Fintype G]
    (hn : (Fintype.card G : ResidueField R) ≠ 0) :
    HasEnoughRootsOfUnity R (Monoid.exponent G) ∧
      IsUnit (Fintype.card G : R) ∧ Nonempty ((G →* Rˣ) ≃* G) := by
  let : HasEnoughRootsOfUnity R (Fintype.card G) :=
    henselian_hasEnoughRootsOfUnity _ hn
  let : HasEnoughRootsOfUnity R (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd R (Group.exponent_dvd_card (G := G))
  exact ⟨inferInstance, (residue_ne_zero_iff_isUnit _).mp (by simpa using hn),
    CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G R⟩

end ThreeAdicPlan
