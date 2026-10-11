/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicFiniteModuleLift
public import Mathlib.RingTheory.Extension.Cotangent.Basic

/-!
# The universal map from a completed original cotangent space

A derivation valued in a module over the completed target factors through
the completion of the original tensor-valued degree-zero space.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicCotangentSpaceLift

open scoped TensorProduct

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (P : Algebra.Extension.{u} R A) (I : Ideal A) [IsNoetherianRing A]
  [Module.Finite A P.CotangentSpace]
  {N : Type*} [AddCommGroup N] [Module R N] [Module P.Ring N] [Module A N]
  [IsScalarTower R P.Ring N] [IsScalarTower P.Ring A N]
  [Module (AdicCompletion I A) N] [IsScalarTower A (AdicCompletion I A) N]

/-- Factor an original derivation through the completed ORIGINAL degree-zero space. -/
def lift (d : Derivation R P.Ring N) :
    AdicCompletion I P.CotangentSpace →ₗ[AdicCompletion I A] N :=
  AdicFiniteModuleLift.lift I (d.liftKaehlerDifferential.liftBaseChange A)

/-- The factorization evaluates each original tensor differential. -/
theorem lift_of_tmul (d : Derivation R P.Ring N) (a : A) (x : P.Ring) :
    lift P I d (AdicCompletion.of I P.CotangentSpace
      (a ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring x)) = a • d x := by
  rw [lift, AdicFiniteModuleLift.lift_of, LinearMap.liftBaseChange_tmul,
    Derivation.liftKaehlerDifferential_comp_D]

omit [IsNoetherianRing A] in
/-- Original tensor differentials determine maps out of the completed cotangent space. -/
theorem ext (f g : AdicCompletion I P.CotangentSpace →ₗ[AdicCompletion I A] N)
    (h : ∀ x, f (AdicCompletion.of I P.CotangentSpace
      (1 ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring x)) =
        g (AdicCompletion.of I P.CotangentSpace
          (1 ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring x))) : f = g := by
  apply AdicFiniteModuleExt.ext_of I
  have he : (f.restrictScalars A).comp (AdicCompletion.of I P.CotangentSpace) =
      (g.restrictScalars A).comp (AdicCompletion.of I P.CotangentSpace) := by
    ext x
    exact h x
  exact fun x ↦ LinearMap.congr_fun he x

/-- The factorization is uniquely determined by original section derivatives. -/
theorem lift_unique (d : Derivation R P.Ring N)
    (f : AdicCompletion I P.CotangentSpace →ₗ[AdicCompletion I A] N)
    (hf : ∀ x, f (AdicCompletion.of I P.CotangentSpace
      (1 ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring x)) = d x) : f = lift P I d := by
  apply ext P I
  intro x
  rw [hf, lift_of_tmul, one_smul]

end FLT.Mazur.AdicCotangentSpaceLift
