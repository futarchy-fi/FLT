/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeBoundaryConnectingMap
public import FLT.Mazur.SubmoduleQuotientScalarReduction

/-!
# Exact boundary lifts from reduced relative classes

Residue vanishing constructs a simultaneous lift with unchanged boundary
values. Relative vanishing makes its discrepancy an internal scalar multiple
of the exact boundary module. Ambient vanishing supplies only an ambient
scalar multiple; it does not identify the two conditions.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.RelativeBoundaryConnectingMap
variable {R A B C : Type*} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
  (b : A →ₗ[R] B) (δ : A →ₗ[R] C)
set_option quotPrecheck false
local notation "K" => (LinearMap.ker b).map δ

/-- A discrepancy in K + P constructs a lift with the exact boundary and discrepancy in P. -/
theorem mem_correction_sup_iff_lift (P : Submodule R C) (u : A) :
    δ u ∈ K ⊔ P ↔ ∃ v : A, b v = b u ∧ δ v ∈ P := by
  constructor
  · intro h
    obtain ⟨y, hy, w, hw, he⟩ := Submodule.mem_sup.mp h
    obtain ⟨z, hz, rfl⟩ := hy
    refine ⟨u - z, ?_, ?_⟩
    · rw [map_sub, LinearMap.mem_ker.mp hz, sub_zero]
    · rw [map_sub, ← he, add_sub_cancel_left]
      exact hw
  · rintro ⟨v, hb, hv⟩
    apply Submodule.mem_sup.mpr
    refine ⟨δ (u - v), ⟨u - v, ?_, rfl⟩, δ v, hv, ?_⟩
    · change b (u - v) = 0
      rw [map_sub, hb, sub_self]
    · rw [map_sub, sub_add_cancel]

/-- The same membership constructs one exact boundary-zero correction family. -/
theorem mem_correction_sup_iff_kernel (P : Submodule R C) (u : A) :
    δ u ∈ K ⊔ P ↔ ∃ z : A, b z = 0 ∧ δ u - δ z ∈ P := by
  rw [mem_correction_sup_iff_lift]
  constructor
  · rintro ⟨v, hb, hv⟩
    refine ⟨u - v, ?_, ?_⟩
    · rw [map_sub, hb, sub_self]
    · rw [map_sub, sub_sub_cancel]
      exact hv
  · rintro ⟨z, hz, he⟩
    exact ⟨u - z, by rw [map_sub, hz, sub_zero], by rwa [map_sub]⟩

variable (J : Ideal R) (N : Submodule R C)

/-- A relative residue class vanishes exactly when an exact boundary lift has error in JN. -/
theorem relative_residue_eq_zero_iff_lift (hKN : (LinearMap.ker b).map δ ≤ N)
    (u : A) (hu : δ u ∈ N) :
    (1 ⊗ₜ[R] relativeClass b δ N u hu :
      (R ⧸ J) ⊗[R] (N ⧸ (K).comap N.subtype)) = 0 ↔
        ∃ v : A, b v = b u ∧ δ v ∈ J • N := by
  unfold relativeClass
  rw [RelativeSubmoduleQuotient.relative_residue_mk_eq_zero_iff_mem J N K hKN]
  exact mem_correction_sup_iff_lift b δ (J • N) u

/-- The relative residue equation constructs a single boundary-zero correction modulo JN. -/
theorem relative_residue_eq_zero_iff_kernel (hKN : (LinearMap.ker b).map δ ≤ N)
    (u : A) (hu : δ u ∈ N) :
    (1 ⊗ₜ[R] relativeClass b δ N u hu :
      (R ⧸ J) ⊗[R] (N ⧸ (K).comap N.subtype)) = 0 ↔
        ∃ z : A, b z = 0 ∧ δ u - δ z ∈ J • N := by
  unfold relativeClass
  rw [RelativeSubmoduleQuotient.relative_residue_mk_eq_zero_iff_mem J N K hKN]
  exact mem_correction_sup_iff_kernel b δ (J • N) u

/-- Ambient residue vanishing gives the weaker error condition JC, with exact boundary values. -/
theorem ambient_residue_eq_zero_iff_lift (u : A) :
    (1 ⊗ₜ[R] (K).mkQ (δ u) : (R ⧸ J) ⊗[R] (C ⧸ K)) = 0 ↔
      ∃ v : A, b v = b u ∧ δ v ∈ J • (⊤ : Submodule R C) := by
  rw [RelativeSubmoduleQuotient.residue_mk_eq_zero_iff]
  exact mem_correction_sup_iff_lift b δ (J • ⊤) u

end FLT.Mazur.RelativeBoundaryConnectingMap
