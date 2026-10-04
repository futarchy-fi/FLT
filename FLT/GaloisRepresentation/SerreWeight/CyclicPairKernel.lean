/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Kernel containment from a cyclic joint character image

If two characters take values in the same finite group and their joint
image is cyclic, surjectivity of the first forces its kernel into the
second. The proof compares the joint exponent with the target cardinality.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.SerreWeight

/-- A surjective character detects every character in a cyclic joint image. -/
theorem ker_le_of_cyclic_pair {G C : Type*} [Group G] [Group C] [Finite C]
    (θ χ : G →* C) (hθ : Function.Surjective θ) [IsCyclic (θ.prod χ).range] :
    θ.ker ≤ χ.ker := by
  let H := (θ.prod χ).range
  let f : H →* C := (MonoidHom.fst C C).comp H.subtype
  have hs : Function.Surjective f := by
    intro c
    obtain ⟨g, hg⟩ := hθ c
    exact ⟨(θ.prod χ).rangeRestrict g, hg⟩
  have hd : Nat.card H ∣ Nat.card C := by
    rw [← IsCyclic.exponent_eq_card]
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Subtype.ext
    apply Prod.ext <;> exact pow_card_eq_one'
  have hi : Function.Injective f :=
    (hs.bijective_of_nat_card_le (Nat.le_of_dvd Nat.card_pos hd)).1
  intro g hg
  have he : (θ.prod χ).rangeRestrict g = 1 := hi (by
    change θ g = 1
    exact hg)
  exact congrArg (fun x : H ↦ x.val.2) he

end GaloisRepresentation.SerreWeight
