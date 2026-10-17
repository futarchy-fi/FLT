/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeSubmoduleQuotient

/-!
# Connecting maps with exact boundary errors

A family of boundary lifts need not be linear. Its discrepancy class is linear
and independent of that choice, after quotienting by discrepancies of exact
boundary-zero families. Its kernel constructs compatible lifts.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.RelativeBoundaryConnectingMap
variable {R A B C D : Type*} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
  (b : A →ₗ[R] B) (δ : A →ₗ[R] C) (N : Submodule R C)
set_option quotPrecheck false
local notation "K" => (LinearMap.ker b).map δ

/-- The exact relative class of a lifted family. -/
def relativeClass (u : A) (hu : δ u ∈ N) : N ⧸ (K).comap N.subtype :=
  ((K).comap N.subtype).mkQ ⟨δ u, hu⟩

/-- Changing a lift by an exact boundary-zero family does not change the relative class. -/
theorem relativeClass_eq (u v : A) (hu : δ u ∈ N) (hv : δ v ∈ N) (h : b u = b v) :
    relativeClass b δ N u hu = relativeClass b δ N v hv := by
  apply RelativeSubmoduleQuotient.inclusion_injective N K
  change (K).mkQ (δ u) = (K).mkQ (δ v)
  apply (sub_eq_zero).mp
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero K).mpr
  exact ⟨u - v, by
    change b (u - v) = 0
    rw [map_sub, h, sub_self], map_sub δ u v⟩

/-- The representative class vanishes exactly when there is a compatible lift of its boundary. -/
theorem relativeClass_eq_zero_iff (u : A) (hu : δ u ∈ N) :
    relativeClass b δ N u hu = 0 ↔ ∃ v : A, b v = b u ∧ δ v = 0 := by
  change ((K).comap N.subtype).mkQ ⟨δ u, hu⟩ = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  change δ u ∈ K ↔ _
  constructor
  · rintro ⟨z, hz, he⟩
    refine ⟨u - z, ?_, ?_⟩
    · rw [map_sub, LinearMap.mem_ker.mp hz, sub_zero]
    · rw [map_sub, he, sub_self]
  · rintro ⟨v, hb, hv⟩
    refine ⟨u - v, ?_, ?_⟩
    · change b (u - v) = 0
      rw [map_sub, hb, sub_self]
    · rw [map_sub, hv, sub_zero]

variable (β : D →ₗ[R] B) (u : D → A)
  (hb : ∀ t, b (u t) = β t) (hN : ∀ t, δ (u t) ∈ N)

/-- The connecting map is linear even when its chosen family of lifts is not. -/
def connecting : D →ₗ[R] N ⧸ (K).comap N.subtype where
  toFun t := relativeClass b δ N (u t) (hN t)
  map_add' s t := by
    have hn : δ (u s + u t) ∈ N := by
      rw [map_add]
      exact N.add_mem (hN s) (hN t)
    rw [relativeClass_eq b δ N (u (s + t)) (u s + u t) (hN _) hn
      (by rw [hb, map_add, map_add, hb, hb])]
    unfold relativeClass
    change ((K).comap N.subtype).mkQ _ = _ + _
    rw [← map_add]
    congr 1
    exact Subtype.ext (map_add δ _ _)
  map_smul' a t := by
    have hn : δ (a • u t) ∈ N := by
      rw [map_smul]
      exact N.smul_mem a (hN t)
    rw [relativeClass_eq b δ N (u (a • t)) (a • u t) (hN _) hn
      (by rw [hb, map_smul, map_smul, hb])]
    unfold relativeClass
    change ((K).comap N.subtype).mkQ _ = a • _
    rw [← map_smul]
    congr 1
    exact Subtype.ext (map_smul δ _ _)

/-- A different simultaneous lift family constructs the same connecting map. -/
theorem connecting_independent (v : D → A)
    (hv : ∀ t, b (v t) = β t) (hNv : ∀ t, δ (v t) ∈ N) :
    connecting b δ N β u hb hN = connecting b δ N β v hv hNv := by
  ext t
  exact relativeClass_eq b δ N (u t) (v t) (hN t) (hNv t) ((hb t).trans (hv t).symm)

/-- Zero connecting class constructs an exact compatible lift of the original boundary value. -/
theorem connecting_eq_zero_iff (t : D) :
    connecting b δ N β u hb hN t = 0 ↔ ∃ v : A, b v = β t ∧ δ v = 0 := by
  change relativeClass b δ N (u t) (hN t) = 0 ↔ _
  rw [relativeClass_eq_zero_iff, hb]

end FLT.Mazur.RelativeBoundaryConnectingMap
