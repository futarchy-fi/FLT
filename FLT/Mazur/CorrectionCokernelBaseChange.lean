/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleErrorBaseChange
public import Mathlib.RingTheory.Flat.Basic

/-!
# Scalar extension of a full correction cokernel

The cokernel of an extended correction operator is canonically the extension
of its original cokernel. This comparison needs no flatness and preserves the
class of every equation vector, including every mixed coordinate.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.CorrectionCokernelBaseChange
variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (F : M →ₗ[R] N) (S : Type*) [CommRing S] [Algebra R S]

/-- The extended quotient map has exactly the extended correction image as kernel. -/
theorem quotient_baseChange_ker :
    LinearMap.ker ((LinearMap.range F).mkQ.baseChange S) =
      LinearMap.range (F.baseChange S) := by
  apply LinearMap.exact_iff.mp
  exact lTensor_exact S (fun x ↦ by simp) (Submodule.mkQ_surjective _)

/-- The full correction cokernel commutes with arbitrary extension of scalars. -/
def equiv : ((S ⊗[R] N) ⧸ LinearMap.range (F.baseChange S)) ≃ₗ[S]
    S ⊗[R] (N ⧸ LinearMap.range F) :=
  (Submodule.quotEquivOfEq _ _ (quotient_baseChange_ker F S).symm).trans
    (((LinearMap.range F).mkQ.baseChange S).quotKerEquivOfSurjective
      (LinearMap.baseChange_surjective S (Submodule.mkQ_surjective _)))

/-- The comparison sends a pure tensor class to the tensor of its original class. -/
theorem equiv_mk_tmul (s : S) (x : N) :
    equiv F S ((LinearMap.range (F.baseChange S)).mkQ (s ⊗ₜ[R] x)) =
      s ⊗ₜ[R] (LinearMap.range F).mkQ x := rfl

/-- Comparison with the quotient projection on arbitrary equation tensors. -/
theorem equiv_comp_mkQ :
    (equiv F S).toLinearMap.comp (LinearMap.range (F.baseChange S)).mkQ =
      (LinearMap.range F).mkQ.baseChange S := rfl

end FLT.Mazur.CorrectionCokernelBaseChange
