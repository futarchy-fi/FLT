/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.IdempotentAugmentationLifting
public import FLT.GroupScheme.HopfTestAlgebraPoints
public import Mathlib.RingTheory.Unramified.Basic

/-! # A Hopf algebra with idempotent augmentation ideal is formally unramified -/

@[expose] public noncomputable section
open WithConv
namespace HopfAlgebra
variable {R A : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A]

/-- Vanishing infinitesimal motion at the identity implies vanishing at every point,
by the group law on algebra-valued points. -/
theorem formallyUnramified_of_idempotent_augmentation
    (hε : IsIdempotentElem (RingHom.ker (Bialgebra.counitAlgHom R A).toRingHom)) :
    Algebra.FormallyUnramified R A := by
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro B _ _ I hI f g hfg
  let : Group (WithConv (A →ₐ[R] B)) := testAlgebraPointGroup R A B
  let : Group (WithConv (A →ₐ[R] B ⧸ I)) := testAlgebraPointGroup R A (B ⧸ I)
  let q := Ideal.Quotient.mkₐ R I
  have hOne : q.comp ((Algebra.ofId R B).comp (Bialgebra.counitAlgHom R A)) =
      (Algebra.ofId R (B ⧸ I)).comp (Bialgebra.counitAlgHom R A) := by
    ext a
    exact q.commutes _
  let φ : WithConv (A →ₐ[R] B) →* WithConv (A →ₐ[R] B ⧸ I) :=
    { toFun := fun x ↦ toConv (q.comp x.ofConv)
      map_one' := congrArg toConv hOne
      map_mul' x y := congrArg toConv (AlgHom.comp_convMul_distrib q x y) }
  have hφ : φ (toConv f) = φ (toConv g) := congrArg toConv hfg
  have hz : φ ((toConv f)⁻¹ * toConv g) = 1 := by
    rw [map_mul, map_inv, hφ, inv_mul_cancel]
  have heq := AlgHom.eq_augmentation_of_idempotent_ker
    (Bialgebra.counitAlgHom R A) hε I hI ((toConv f)⁻¹ * toConv g).ofConv
    (show q.comp ((toConv f)⁻¹ * toConv g).ofConv =
      q.comp ((Algebra.ofId R B).comp (Bialgebra.counitAlgHom R A)) from
      (congrArg ofConv hz).trans hOne.symm)
  have hunit : (toConv f)⁻¹ * toConv g = 1 := congrArg toConv heq
  exact toConv_injective ((inv_mul_eq_one).mp hunit)
end HopfAlgebra
