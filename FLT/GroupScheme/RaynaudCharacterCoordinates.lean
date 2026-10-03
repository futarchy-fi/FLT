/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCharacterFunctions

/-!
# Geometric evaluation of integral character coordinates

Embed the actual coordinate ring in its equivariant generic functions.
Evaluation preserves the counit and carries integral model maps to
precomposition by the prescribed generic point maps.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] [PerfectField K]

/-- The scalar tower on equivariant generic functions. -/
instance FF.characterCoordinatesTower (X : FF R K) : IsScalarTower R K
    (X.Points →[AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K] AlgebraicClosure K) := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  ext x
  exact IsScalarTower.algebraMap_apply R K (AlgebraicClosure K) r

/-- Integral coordinates as actual equivariant functions on generic points. -/
def FF.characterCoordinates (X : FF R K) : X.CoordinateRing →ₐ[R]
    (X.Points →[AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K] AlgebraicClosure K) :=
  (X.genericCoordinates.symm.toAlgEquiv.toAlgHom.restrictScalars R).comp
    Algebra.TensorProduct.includeRight

/-- Geometric evaluation is injective on integral coordinates. -/
theorem FF.characterCoordinates_injective [IsFractionRing R K] (X : FF R K) :
    Function.Injective X.characterCoordinates :=
  X.genericCoordinates.symm.injective.comp
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K))

/-- Evaluation at the identity is the original integral counit. -/
theorem FF.characterCoordinates_counit (X : FF R K) (a : X.CoordinateRing) :
    X.characterCoordinates a 0 = algebraMap R (AlgebraicClosure K)
      (Coalgebra.counit (R := R) a) := by
  let := GaloisModule.GenericFiber.hopfAlgebra K (AlgebraicClosure K) X.Points
  have h := CoalgHomClass.counit_comp_apply X.genericCoordinates.symm.toBialgHom
    (1 ⊗ₜ[R] a)
  have h' := congrArg (algebraMap K (AlgebraicClosure K)) h
  change algebraMap K (AlgebraicClosure K)
    (GaloisModule.GenericFiber.counitAlgHom K (AlgebraicClosure K) X.Points
      (X.characterCoordinates a)) = _ at h'
  rw [GaloisModule.GenericFiber.algebraMap_counitAlgHom] at h'
  simpa only [TensorProduct.counit_tmul, map_one, Bialgebra.counit_one, one_mul, mul_one,
    Algebra.smul_def, ← IsScalarTower.algebraMap_apply R K (AlgebraicClosure K)] using h'

/-- Evaluation at a chosen geometric point agrees with the generic coordinate map. -/
theorem FF.characterCoordinates_points (X : FF R K) (a : X.CoordinateRing)
    (x : Additive (K ⊗[R] X.CoordinateRing →ₐ[K] AlgebraicClosure K)) :
    X.characterCoordinates a (X.points x) = x.toMul (1 ⊗ₜ[R] a) := by
  have h := X.eval_genericCoordinates (X.characterCoordinates a) x.toMul
  change x.toMul (X.genericCoordinates (X.genericCoordinates.symm (1 ⊗ₜ[R] a))) = _ at h
  simpa using h.symm

/-- Coordinate pullback is precomposition by the actual generic point map. -/
theorem ModelHom.characterCoordinates_apply {X Y : FF R K} (f : ModelHom X Y)
    (a : Y.CoordinateRing) (x : X.Points) :
    X.characterCoordinates (f a) x = Y.characterCoordinates a (genericHom f x) := by
  obtain ⟨p, rfl⟩ := X.points_bijective.2 x
  rw [genericHom_points, FF.characterCoordinates_points, FF.characterCoordinates_points]
  rfl

end ThreeAdicPlan
