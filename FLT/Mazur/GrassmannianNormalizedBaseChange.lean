/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

import all Mathlib.RingTheory.Grassmannian

public import FLT.Mazur.GrassmannianFunctorLocalizedChart

/-!
# Normalized evaluation computes the actual Grassmannian base change

An isomorphism of the original quotient with a finite free module transports
its tensor quotient map to normalized coordinates. Equality is proved for the
entire kernel, with no flatness assumption on the coefficient algebra map.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A B M : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [AddCommGroup M] [Module R M] {d : ℕ}

/-- Scalar extension of a normalized quotient, in standard free-module coordinates. -/
def normalizedQuotientBaseChange (q : (A ⊗[R] M) →ₗ[A] (Fin d → A)) :
    (B ⊗[R] M) →ₗ[B] (Fin d → B) :=
  (TensorProduct.piScalarRight A B B (Fin d)).toLinearMap.comp
    ((q.baseChange B).comp
      (AlgebraTensorModule.cancelBaseChange R A B B M).symm.toLinearMap)

/-- Its pure-tensor values only apply the coefficient homomorphism to quotient coordinates. -/
theorem normalizedQuotientBaseChange_tmul (q : (A ⊗[R] M) →ₗ[A] (Fin d → A))
    (b : B) (m : M) :
    normalizedQuotientBaseChange (B := B) q (b ⊗ₜ[R] m) =
      fun j ↦ algebraMap A B (q (1 ⊗ₜ[R] m) j) * b := by
  simp only [normalizedQuotientBaseChange, LinearMap.comp_apply, LinearEquiv.coe_coe,
    AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul, Algebra.smul_def]

/-- The normalized map has the full kernel of the actual Grassmannian functor image. -/
theorem grassmannian_map_normalized_kernel (N : Module.Grassmannian A (A ⊗[R] M) d)
    (q : (A ⊗[R] M) →ₗ[A] (Fin d → A))
    (e : ((A ⊗[R] M) ⧸ N.toSubmodule) ≃ₗ[A] (Fin d → A))
    (he : e.toLinearMap.comp N.toSubmodule.mkQ = q) :
    (Module.Grassmannian.map (IsScalarTower.toAlgHom R A B) N).toSubmodule =
      (normalizedQuotientBaseChange (B := B) q).ker := by
  have hN : (Module.Grassmannian.map (IsScalarTower.toAlgHom R A B) N).toSubmodule =
      (Module.Grassmannian.baseChangeMkQ B N.toSubmodule).ker := by
    have ha : (IsScalarTower.toAlgHom R A B).toAlgebra = ‹Algebra A B› :=
      Algebra.algebra_ext _ _ fun _ ↦ rfl
    exact (Module.Grassmannian.map_toSubmodule _ N).trans
      (baseChangeMkQ_ker_algebra_congr _ _ ha _ _ N.toSubmodule)
  let E := (e.baseChange A B).trans (TensorProduct.piScalarRight A B B (Fin d))
  have hc : E.toLinearMap.comp (Module.Grassmannian.baseChangeMkQ B N.toSubmodule) =
      normalizedQuotientBaseChange (B := B) q := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul b m =>
      simp only [E, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
        Module.Grassmannian.baseChangeMkQ, AlgebraTensorModule.cancelBaseChange_symm_tmul,
        LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul,
        normalizedQuotientBaseChange_tmul, TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul, Algebra.smul_def]
      exact congrArg (fun v : Fin d → A ↦ fun j ↦ algebraMap A B (v j) * b)
        (LinearMap.congr_fun he (1 ⊗ₜ[R] m))
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [hN, ← hc, LinearEquiv.ker_comp]

end FLT.Mazur.GrassmannianChart
