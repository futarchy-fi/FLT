/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalCompletionModel
public import FLT.Mazur.TensorAlgebraSemilinearEquiv
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# Finite original modules in a local completion model

A semilinear identification of a completed original module with a model
module gives a linear identification after extension by the actual local
ring action on the model.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.LocalCompletionModelFiniteEquiv

open TensorProduct

universe u

variable {R A D : Type u} [CommRing R] [CommRing A] [CommRing D]
  [Algebra R A] [Algebra R D] [IsLocalRing A] [IsNoetherianRing A]
  (e : AdicCompletion (IsLocalRing.maximalIdeal A) A ≃ₐ[R] D)
  (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
  {N : Type u} [AddCommGroup N] [Module D N]

attribute [local instance] TensorAlgebraSemilinearEquiv.forwardInverse
  TensorAlgebraSemilinearEquiv.reverseInverse

variable (f : LinearEquiv e.toRingHom (σ' := e.symm.toRingHom)
  (AdicCompletion (IsLocalRing.maximalIdeal A) M) N)

/-- A completed-module comparison is linear over the model for its actual local-ring action. -/
def equiv :
    let _ := (LocalCompletionModel.scalars e).toAlgebra
    (D ⊗[A] M) ≃ₗ[D] N := by
  let _ := (LocalCompletionModel.scalars e).toAlgebra
  let eA := LocalCompletionModel.localAlgebraEquivalence e
  let _ : RingHomCompTriple eA.symm.toRingHom e.toRingHom (RingHom.id D) :=
    ⟨RingHom.ext e.apply_symm_apply⟩
  let _ : RingHomCompTriple e.symm.toRingHom eA.toRingHom (RingHom.id D) :=
    ⟨RingHom.ext e.apply_symm_apply⟩
  exact ((TensorAlgebraSemilinearEquiv.equiv eA M).symm.trans
    (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian
      (IsLocalRing.maximalIdeal A) M)).trans f

end FLT.Mazur.LocalCompletionModelFiniteEquiv
