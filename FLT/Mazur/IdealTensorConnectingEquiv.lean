/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealTensorConnectingMap

/-!
# Ideal obstructions as reduced presentation kernels

The connecting map is surjective for every exact presentation with flat
middle term. When its first map is injective, it is a linear equivalence.
No finiteness assumptions on the presentation or the base ring are needed.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.IdealTensorConnectingEquiv
open IdealTensorConnectingMap
variable {R P N M : Type*} [CommRing R]
  [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
  [AddCommGroup M] [Module R M] [Module.Flat R N]
  (f : P →ₗ[R] N) (q : N →ₗ[R] M)
  (he : Function.Exact f q) (hq : Function.Surjective q) (I : Ideal R)

/-- Every ideal obstruction comes from an actual reduced presentation relation. -/
theorem connecting_surjective : Function.Surjective (connecting f q he hq I) := by
  intro z
  obtain ⟨t, u, ht, hu, hz⟩ :=
    IdealTensorPresentationLift.lift_ideal_kernel f q he hq I z.val z.property
  refine ⟨⟨I.mkQ.rTensor P u, hz⟩, Subtype.ext ?_⟩
  exact (connecting_eq f q he hq I _ u t rfl hu).trans ht

/-- An injective presentation has no additional relations in the connecting kernel. -/
theorem connecting_injective (hf : Function.Injective f) :
    Function.Injective (connecting f q he hq I) := by
  have hz (z : (f.lTensor (R ⧸ I)).ker) (h : connecting f q he hq I z = 0) : z = 0 := by
    apply Subtype.ext
    have ht : q.lTensor I (lifts f q he hq I z).2 = 0 := congrArg Subtype.val h
    have hu := IdealTensorPresentationLift.quotient_zero_of_ideal_zero f q he hq I hf
      (lifts f q he hq I z).2 (lifts f q he hq I z).1
      (lifts_spec f q he hq I z).2.1.symm ht
    exact (lifts_spec f q he hq I z).1.symm.trans hu
  intro z w h
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, h, sub_self]

/-- The two actual obstruction modules of a flat presentation are linearly equivalent. -/
def connectingEquiv (hf : Function.Injective f) :
    (f.lTensor (R ⧸ I)).ker ≃ₗ[R] (I.subtype.rTensor M).ker :=
  LinearEquiv.ofBijective (connecting f q he hq I)
    ⟨connecting_injective f q he hq I hf, connecting_surjective f q he hq I⟩

end FLT.Mazur.IdealTensorConnectingEquiv
