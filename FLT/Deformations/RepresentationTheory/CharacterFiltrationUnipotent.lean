/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.CharacterFiltrationDeterminant

/-! # Unipotent elements act trivially on both characters of an exact filtration -/

@[expose] public noncomputable section
namespace GaloisRep.CharacterFiltration
variable {K k V : Type*} [Field K] [Field k] [TopologicalSpace k]
  [AddCommGroup V] [Module k V] {ρ : GaloisRep K k V}
  (F : CharacterFiltration ρ) (g : Field.absoluteGaloisGroup K)

/-- Square-zero deviation from identity forces both actual character values to be one. -/
theorem values_eq_one_of_sq_zero (hsq : (ρ g - 1) ^ 2 = 0) :
    F.χ₁ g 1 = 1 ∧ F.χ₂ g 1 = 1 := by
  have hi (a : k) : (ρ g - 1) (F.i a) = F.i ((F.χ₁ g 1 - 1) * a) := by
    change ρ g (F.i a) - F.i a = F.i ((F.χ₁ g 1 - 1) * a)
    rw [F.i_equivariant, line_apply, sub_mul, one_mul, map_sub]
  have hq (v : V) : F.q ((ρ g - 1) v) = (F.χ₂ g 1 - 1) * F.q v := by
    change F.q (ρ g v - v) = (F.χ₂ g 1 - 1) * F.q v
    rw [map_sub, F.q_equivariant, line_apply, sub_mul, one_mul]
  constructor
  · have h := congrArg (fun f : Module.End k V ↦ f (F.i 1)) hsq
    change (ρ g - 1) ((ρ g - 1) (F.i 1)) = 0 at h
    rw [hi, hi, mul_one] at h
    have he := F.i_injective (h.trans (map_zero F.i).symm)
    exact sub_eq_zero.mp (mul_self_eq_zero.mp he)
  · obtain ⟨v, hv⟩ := F.q_surjective 1
    have h := congrArg (fun f : Module.End k V ↦ F.q (f v)) hsq
    change F.q ((ρ g - 1) ((ρ g - 1) v)) = F.q 0 at h
    rw [hq, hq, hv, map_zero, mul_one] at h
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h)

/-- Both character representations are the identity on the unipotent element. -/
theorem characters_eq_one_of_sq_zero (hsq : (ρ g - 1) ^ 2 = 0) :
    F.χ₁ g = 1 ∧ F.χ₂ g = 1 := by
  obtain ⟨h₁, h₂⟩ := F.values_eq_one_of_sq_zero g hsq
  constructor
  · apply LinearMap.ext
    intro a
    rw [line_apply, h₁, one_mul]
    rfl
  · apply LinearMap.ext
    intro a
    rw [line_apply, h₂, one_mul]
    rfl

end GaloisRep.CharacterFiltration
