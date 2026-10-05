/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTensorCocycle

/-!
# Extending last-pair transport from tensor generators

An additive section diagram that intertwines the overlap on pure tensors
intertwines it on every coefficient tensor. This isolates tensor induction
from the concrete sheaf module instances used in geometric descent.
-/

@[expose] public noncomputable section
open TensorProduct
universe u
namespace FLT.Mazur.AffineTensorTransportAdditivity

/-- A last-pair transport formula on generators determines the full additive diagram. -/
theorem transport_coefficients {A B C N L P Q : Type u}
    [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup N] [Module A N]
    [Module B N] [IsScalarTower A B N]
    [AddCommGroup L] [AddCommGroup P] [AddCommGroup Q] [DistribSMul C P]
    (F : P →+ Q) (G : L →+ P) (K : B ⊗[A] N ≃+ L)
    (D : B ⊗[A] (B ⊗[A] N) ≃+ Q) (E : N ⊗[A] B ≃ₗ[B] B ⊗[A] N)
    (c : C) (t : B)
    (h : ∀ a n, F (c • G (K (a ⊗ₜ[A] n))) = D (a ⊗ₜ[A] E (n ⊗ₜ[A] t)))
    (x : B ⊗[A] N) :
    F (c • G (K x)) = D ((E.toLinearMap.restrictScalars A).lTensor B
      ((TensorProduct.assoc A B N B) (x ⊗ₜ[A] t))) := by
  induction x using TensorProduct.inductionOn with
  | tmul a n => exact h a n
  | add x y hx hy => simp only [add_tmul, map_add, smul_add, hx, hy]

end FLT.Mazur.AffineTensorTransportAdditivity
