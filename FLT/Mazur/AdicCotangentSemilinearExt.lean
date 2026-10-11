/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCotangentSpaceLift

/-!
# Original differentials determine semilinear maps of completed spaces

The finite original cotangent space generates its completion even when
the target scalar ring changes by an arbitrary ring homomorphism.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicCotangentSemilinearExt

open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

universe u

variable {R A : Type u} {S : Type*} [CommRing R] [CommRing A] [Algebra R A] [Semiring S]
  (P : Algebra.Extension.{u} R A) (I : Ideal A) [Module.Finite A P.CotangentSpace]
  {N : Type*} [AddCommGroup N] [Module S N] (e : AdicCompletion I A →+* S)

/-- Original section differentials determine a completed semilinear cotangent map. -/
theorem ext (f g : AdicCompletion I P.CotangentSpace →ₛₗ[e] N)
    (h : ∀ x, f (AdicCompletion.of I P.CotangentSpace
      (1 ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring x)) =
        g (AdicCompletion.of I P.CotangentSpace
          (1 ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring x))) : f = g := by
  let _ : Module (AdicCompletion I A) N := Module.compHom _ e
  let _ : Module A N := Module.compHom _ (algebraMap A (AdicCompletion I A))
  let _ : Module P.Ring N := Module.compHom _ (algebraMap P.Ring A)
  let _ : Module R N := Module.compHom _ (algebraMap R P.Ring)
  let _ : IsScalarTower A (AdicCompletion I A) N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : IsScalarTower P.Ring A N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : IsScalarTower R P.Ring N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let f' : AdicCompletion I P.CotangentSpace →ₗ[AdicCompletion I A] N :=
    { f.toAddHom with map_smul' := fun a x ↦ f.map_smulₛₗ a x }
  let g' : AdicCompletion I P.CotangentSpace →ₗ[AdicCompletion I A] N :=
    { g.toAddHom with map_smul' := fun a x ↦ g.map_smulₛₗ a x }
  have he : f' = g' := by
    apply AdicCotangentSpaceLift.ext P I
    intro x
    exact h x
  exact LinearMap.ext fun x ↦ LinearMap.congr_fun he x

end FLT.Mazur.AdicCotangentSemilinearExt
