/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeComponentLabel
public import FLT.Mazur.EllipticSingularVariableChange

/-!
# Residues of changes between normalized split nodes

The origin is the unique singular point of a normalized split node. Hence
an integral change between normalized split models has translations in the
maximal ideal. Its shear either preserves or exchanges the two tangents.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

/-- A variable change between normalized split depth models has small translations. -/
theorem splitNodeDepth_change_translation_mem {R : Type*} [CommRing R] [IsLocalRing R]
    {W : WeierstrassCurve R} {π π' : R} {n m : ℕ}
    (D : SplitNodeDepth W π n) (C : VariableChange R)
    (D' : SplitNodeDepth (C • W) π' m) :
    C.r ∈ maximalIdeal R ∧ C.t ∈ maximalIdeal R := by
  have heq : C.map (residue R) • W.map (residue R) = (C • W).map (residue R) :=
    map_variableChange W C (residue R)
  have hv := singular_of_variableChange_coefficients (W.map (residue R)) (C.map (residue R))
    (heq ▸ (show ((C • W).map (residue R)).a₃ = 0 from
      (residue_eq_zero_iff _).mpr (Ideal.pow_le_self (by omega) D'.a₃_mem)))
    (heq ▸ (show ((C • W).map (residue R)).a₄ = 0 from
      (residue_eq_zero_iff _).mpr (Ideal.pow_le_self (by omega) D'.a₄_mem)))
    (heq ▸ (show ((C • W).map (residue R)).a₆ = 0 from
      (residue_eq_zero_iff _).mpr
        (Ideal.pow_le_self (Nat.ne_of_gt D'.depth_pos) D'.a₆_mem)))
  have hu := eq_zero_of_normalized_singular (W.map (residue R))
    ((residue_eq_zero_iff _).mpr (Ideal.pow_le_self (by omega) D.a₃_mem))
    ((residue_eq_zero_iff _).mpr (Ideal.pow_le_self (by omega) D.a₄_mem))
    ((residue_eq_zero_iff _).mpr
      (Ideal.pow_le_self (Nat.ne_of_gt D.depth_pos) D.a₆_mem)) hv.1 hv.2
  exact ⟨(residue_eq_zero_iff _).mp hu.1, (residue_eq_zero_iff _).mp hu.2⟩

/-- The residual shear between split depth models preserves or exchanges tangent directions. -/
theorem splitNodeDepth_change_shear_cases {R : Type*} [CommRing R] [IsLocalRing R]
    {W : WeierstrassCurve R} {π π' : R} {n m : ℕ}
    (D : SplitNodeDepth W π n) (C : VariableChange R)
    (D' : SplitNodeDepth (C • W) π' m) :
    C.s ∈ maximalIdeal R ∨ C.s + W.a₁ ∈ maximalIdeal R := by
  have hr := (splitNodeDepth_change_translation_mem D C D').1
  have h2 : W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2 ∈ maximalIdeal R := by
    have h := D'.a₂_mem
    rw [variableChange_a₂] at h
    exact ((maximalIdeal R).unit_mul_mem_iff_mem (C.u⁻¹.isUnit.pow 2)).mp h
  have he := (residue_eq_zero_iff _).mpr h2
  have he' : residue R C.s * (residue R C.s + residue R W.a₁) = 0 := by
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat,
      (residue_eq_zero_iff _).mpr D.a₂_mem, (residue_eq_zero_iff _).mpr hr] at he
    linear_combination -he
  rcases mul_eq_zero.mp he' with hs | hs
  · exact Or.inl ((residue_eq_zero_iff _).mp hs)
  · exact Or.inr ((residue_eq_zero_iff _).mp (by simpa using hs))

end FLT.Mazur
