/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.Card

/-!
# Finite faithful markings turn label assignments into automorphisms

If one faithful marking has all its values in a second faithful marking of
the same finite group, their actual matching function is a group automorphism.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteFaithfulMarkingRelabel
universe u v
variable {L : Type u} [Group L] [Finite L] {A : Type v} [Monoid A]
  (m v : L →* A) (hm : Function.Injective m) (hv : Function.Injective v)

include hm hv

/-- A matching of two faithful finite markings is induced by a unique label automorphism. -/
theorem existsUnique_relabel (a : L → L) (ha : ∀ i, m (a i) = v i) :
    ∃! r : MulAut L, ∀ i, m (r i) = v i := by
  let k : L →* L :=
    { toFun := a
      map_one' := hm (by rw [ha, map_one, map_one])
      map_mul' := fun i j => hm (by rw [ha, map_mul, map_mul, ha, ha]) }
  have hi : Function.Injective k := by
    intro i j hij
    apply hv
    rw [← ha, ← ha]
    exact congrArg m hij
  let r : MulAut L := MulEquiv.ofBijective k ⟨hi, Finite.surjective_of_injective hi⟩
  refine ⟨r, ha, fun t ht => ?_⟩
  apply MulEquiv.ext
  exact fun i => hm ((ht i).trans (ha i).symm)

end FLT.Mazur.FiniteFaithfulMarkingRelabel
