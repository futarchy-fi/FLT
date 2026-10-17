/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Prod

/-!
# Eliminating a surjective block of a paired linear system

For `(b, d)`, the remaining cokernel is `C / d(ker b)`. The comparison into
its full cokernel is always injective and is surjective when `b` is. Thus no
mixed equation is discarded by eliminating the boundary block.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PairedCokernel
variable {R A B C : Type*} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C] (b : A →ₗ[R] B) (d : A →ₗ[R] C)

/-- Insert a mixed coordinate into the full cokernel. -/
def mixedMap : C →ₗ[R] ((B × C) ⧸ LinearMap.range (b.prod d)) :=
  (LinearMap.range (b.prod d)).mkQ.comp (LinearMap.inr R B C)

/-- Only discrepancies of exact boundary-kernel elements vanish under insertion. -/
theorem ker_mixedMap : LinearMap.ker (mixedMap b d) = (LinearMap.ker b).map d := by
  ext c
  change (LinearMap.range (b.prod d)).mkQ (0, c) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, congrArg Prod.fst ha, congrArg Prod.snd ha⟩
  · rintro ⟨a, hb, rfl⟩
    exact ⟨a, Prod.ext hb rfl⟩

/-- The mixed quotient embeds canonically in the full correction cokernel. -/
def inclusion : (C ⧸ (LinearMap.ker b).map d) →ₗ[R]
    ((B × C) ⧸ LinearMap.range (b.prod d)) :=
  ((LinearMap.ker b).map d).liftQ (mixedMap b d) (ker_mixedMap b d).ge

/-- Insertion on a mixed representative. -/
theorem inclusion_mk (c : C) :
    inclusion b d (((LinearMap.ker b).map d).mkQ c) =
      (LinearMap.range (b.prod d)).mkQ (0, c) := rfl

/-- Eliminating the boundary block loses no mixed obstruction. -/
theorem inclusion_injective : Function.Injective (inclusion b d) := by
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ (ker_mixedMap b d).le

/-- Subtracting any boundary lift gives a representative in the mixed quotient. -/
theorem representative (a : A) (c : C) :
    inclusion b d (((LinearMap.ker b).map d).mkQ (c - d a)) =
      (LinearMap.range (b.prod d)).mkQ (b a, c) := by
  rw [inclusion_mk]
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨-a, ?_⟩
  apply Prod.ext
  · change b (-a) = 0 - b a
    rw [map_neg, zero_sub]
  · change d (-a) = c - d a - c
    rw [map_neg, sub_sub_cancel_left]

/-- A surjective boundary block makes mixed insertion surjective. -/
theorem inclusion_surjective (hb : Function.Surjective b) :
    Function.Surjective (inclusion b d) := by
  intro x
  obtain ⟨⟨y, z⟩, rfl⟩ := (LinearMap.range (b.prod d)).mkQ_surjective x
  obtain ⟨a, rfl⟩ := hb y
  exact ⟨((LinearMap.ker b).map d).mkQ (z - d a), representative b d a z⟩

/-- Canonical elimination of the boundary block, retaining the full mixed quotient. -/
def equiv (hb : Function.Surjective b) :
    (C ⧸ (LinearMap.ker b).map d) ≃ₗ[R]
      ((B × C) ⧸ LinearMap.range (b.prod d)) :=
  LinearEquiv.ofBijective (inclusion b d)
    ⟨inclusion_injective b d, inclusion_surjective b d hb⟩

/-- The boundary-only class is the negative discrepancy of any actual boundary lift. -/
theorem boundary_eq_zero_iff (a : A) :
    (LinearMap.range (b.prod d)).mkQ (b a, 0) = 0 ↔
      d a ∈ (LinearMap.ker b).map d := by
  rw [← representative b d a 0, map_eq_zero_iff _ (inclusion_injective b d),
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, zero_sub, Submodule.neg_mem_iff]

end FLT.Mazur.PairedCokernel
