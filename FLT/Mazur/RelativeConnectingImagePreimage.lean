/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeBoundaryConnectingMap

/-!
# Original representatives of the relative connecting image

The preimage of the actual obstruction image consists exactly of discrepancies
of chart families whose boundary comes from an original boundary section.
This module is smaller than the full exact boundary module in general.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.RelativeBoundaryConnectingMap
variable {R A B C D : Type*} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
  (b : A →ₗ[R] B) (δ : A →ₗ[R] C) (N : Submodule R C)
  (β : D →ₗ[R] B) (u : D → A)
  (hb : ∀ t, b (u t) = β t) (hN : ∀ t, δ (u t) ∈ N)
set_option quotPrecheck false
local notation "K" => (LinearMap.ker b).map δ

/-- Discrepancies of original families with boundary values in the prescribed boundary image. -/
def compatibleDiscrepancies : Submodule R C := ((LinearMap.range β).comap b).map δ

/-- Every boundary-zero correction is a compatible discrepancy. -/
theorem correction_le_compatibleDiscrepancies : K ≤ compatibleDiscrepancies b δ β := by
  apply Submodule.map_mono
  intro z hz
  change b z ∈ LinearMap.range β
  rw [LinearMap.mem_ker.mp hz]
  exact Submodule.zero_mem _

include hb hN in
/-- Exact lift errors and exact boundary-zero corrections place every compatible error in N. -/
theorem compatibleDiscrepancies_le (hKN : (LinearMap.ker b).map δ ≤ N) :
    compatibleDiscrepancies b δ β ≤ N := by
  rintro _ ⟨v, ⟨t, ht⟩, rfl⟩
  have hz : v - u t ∈ LinearMap.ker b := by
    change b (v - u t) = 0
    rw [map_sub, hb, ht, sub_self]
  have hd := N.add_mem (hKN (show δ (v - u t) ∈ K from ⟨_, hz, rfl⟩)) (hN t)
  simpa only [map_sub, sub_add_cancel] using hd

/-- Lifting an image class constructs one original compatible family with the exact discrepancy. -/
theorem mem_connecting_preimage_iff (x : N) :
    ((K).comap N.subtype).mkQ x ∈ LinearMap.range (connecting b δ N β u hb hN) ↔
      ∃ v : A, b v ∈ LinearMap.range β ∧ δ v = x.val := by
  constructor
  · rintro ⟨t, ht⟩
    have he : ((K).comap N.subtype).mkQ ⟨δ (u t), hN t⟩ =
        ((K).comap N.subtype).mkQ x := ht
    have hd : (⟨δ (u t), hN t⟩ : N) - x ∈ (K).comap N.subtype := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change ((K).comap N.subtype).mkQ _ = 0
      rw [map_sub, he, sub_self]
    obtain ⟨z, hz, hδ⟩ := hd
    refine ⟨u t - z, ?_, ?_⟩
    · rw [map_sub, LinearMap.mem_ker.mp hz, sub_zero, hb]
      exact ⟨t, rfl⟩
    · change δ z = δ (u t) - x.val at hδ
      rw [map_sub, hδ, sub_sub_cancel]
  · rintro ⟨v, ⟨t, ht⟩, hv⟩
    have hvN : δ v ∈ N := hv.symm ▸ x.property
    refine ⟨t, ?_⟩
    change relativeClass b δ N (u t) (hN t) = _
    rw [relativeClass_eq b δ N (u t) v (hN t) hvN ((hb t).trans ht)]
    unfold relativeClass
    congr 1
    exact Subtype.ext hv

/-- The preimage of the actual connecting image is computed before any scalar reduction. -/
theorem connecting_range_comap :
    (LinearMap.range (connecting b δ N β u hb hN)).comap ((K).comap N.subtype).mkQ =
      (compatibleDiscrepancies b δ β).comap N.subtype := by
  ext x
  exact mem_connecting_preimage_iff b δ N β u hb hN x

end FLT.Mazur.RelativeBoundaryConnectingMap
