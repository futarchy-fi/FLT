/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InfinitesimalCotangentDerivation

/-!
# Infinitesimalization preserves the original degree-zero cotangent space

Descending the original tensor-valued derivation gives an explicit inverse
to the genuine cotangent-space map of the infinitesimal extension.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.InfinitesimalCotangentSpaceEquiv

open Algebra.Extension
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (P : Algebra.Extension R A)

/-- Infinitesimal coefficients act on original differentials through the target. -/
local instance spaceModule : Module P.infinitesimal.Ring P.CotangentSpace :=
  Module.compHom P.CotangentSpace (algebraMap P.infinitesimal.Ring A)

/-- The action factors through the original target algebra. -/
local instance spaceTower : IsScalarTower P.infinitesimal.Ring A P.CotangentSpace :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Descending the original derivation gives the inverse degree-zero map. -/
def inverse : P.infinitesimal.CotangentSpace →ₗ[A] P.CotangentSpace :=
  (InfinitesimalCotangentDerivation.descended P).liftKaehlerDifferential.liftBaseChange A

/-- The inverse retains the original differential of a representative. -/
theorem inverse_tmul (a : A) (x : P.Ring) :
    inverse P (a ⊗ₜ[P.infinitesimal.Ring]
      KaehlerDifferential.D R P.infinitesimal.Ring (P.toInfinitesimal.toAlgHom x)) =
        a ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring x := by
  rw [inverse, LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D,
    InfinitesimalCotangentDerivation.descended_mk, TensorProduct.smul_tmul', smul_eq_mul,
    mul_one]

/-- The descended derivative is a left inverse on the entire original cotangent space. -/
theorem inverse_comp : (inverse P).comp (CotangentSpace.map P.toInfinitesimal) =
    LinearMap.id := by
  ext x
  change inverse P (CotangentSpace.map P.toInfinitesimal
    (1 ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring x)) = _
  rw [CotangentSpace.map_tmul, inverse_tmul]
  rfl

/-- Every infinitesimal differential comes from an original representative. -/
theorem map_comp_inverse : (CotangentSpace.map P.toInfinitesimal).comp (inverse P) =
    LinearMap.id := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change CotangentSpace.map P.toInfinitesimal
    (inverse P (1 ⊗ₜ[P.infinitesimal.Ring]
      KaehlerDifferential.D R P.infinitesimal.Ring (P.toInfinitesimal.toAlgHom x))) = _
  rw [inverse_tmul, CotangentSpace.map_tmul]
  rfl

/-- The original degree-zero space is unchanged by quotienting by the relation square. -/
def equiv : P.CotangentSpace ≃ₗ[A] P.infinitesimal.CotangentSpace :=
  { CotangentSpace.map P.toInfinitesimal with
    invFun := inverse P
    left_inv := fun x ↦ LinearMap.congr_fun (inverse_comp P) x
    right_inv := fun x ↦ LinearMap.congr_fun (map_comp_inverse P) x }

/-- The comparison is the genuine extension map on all original cotangent vectors. -/
@[simp] theorem equiv_apply (x : P.CotangentSpace) :
    equiv P x = CotangentSpace.map P.toInfinitesimal x := rfl

end FLT.Mazur.InfinitesimalCotangentSpaceEquiv
