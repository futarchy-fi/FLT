/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantFiniteFlat
public import FLT.GroupScheme.IntegralCartierDual

/-!
# Coordinates of the canonical constant integral model

For a trivial finite Galois module, the equivariant generic functions take
rational values. Their integral closure is precisely the functions with
values in the integral base ring.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable (A : Type) [AddCommGroup A] [Finite A]

/-- Rational-valued functions give equivariant functions on a constant module. -/
def constantGenericMap : (A → ℚ) →ₐ[ℚ] (constantPoints A).GenericCoordinateAlgebra where
  toFun f :=
    { toFun := fun a ↦ algebraMap ℚ (AlgebraicClosure ℚ) (f a)
      map_smul' := fun σ a ↦ (σ.commutes (f a)).symm }
  map_zero' := by ext a; exact map_zero (algebraMap ℚ (AlgebraicClosure ℚ))
  map_one' := by ext a; exact map_one (algebraMap ℚ (AlgebraicClosure ℚ))
  map_add' f g := by ext a; exact map_add (algebraMap ℚ (AlgebraicClosure ℚ)) (f a) (g a)
  map_mul' f g := by ext a; exact map_mul (algebraMap ℚ (AlgebraicClosure ℚ)) (f a) (g a)
  commutes' r := rfl

/-- Equivariant functions on a constant module are exactly the rational functions. -/
theorem constantGenericMap_bijective : Function.Bijective (constantGenericMap A) := by
  constructor
  · intro f g h
    funext a
    exact (algebraMap ℚ (AlgebraicClosure ℚ)).injective (congrArg (fun z ↦ z a) h)
  · intro f
    have h (a : A) : ∃ q : ℚ, algebraMap ℚ (AlgebraicClosure ℚ) q = f a := by
      apply (InfiniteGalois.mem_range_algebraMap_iff_fixed (f a)).mpr
      intro σ
      exact (f.map_smul σ a).symm
    choose q hq using h
    exact ⟨q, by ext a; exact hq a⟩

/-- The generic coordinate algebra of a constant group is its rational function algebra. -/
def constantGenericEquiv : (A → ℚ) ≃ₐ[ℚ] (constantPoints A).GenericCoordinateAlgebra :=
  AlgEquiv.ofBijective (constantGenericMap A) (constantGenericMap_bijective A)

/-- Scalar extension of a finite function algebra lands in the integral closure. -/
def integralPiMap (R K I : Type*) [CommRing R] [Field K] [Algebra R K] [Finite I] :
    (I → R) →ₐ[R] integralClosure R (I → K) :=
  let f : (I → R) →ₐ[R] (I → K) :=
    AlgHom.pi fun i ↦ (Algebra.ofId R K).comp (Pi.evalAlgHom R (fun _ : I ↦ R) i)
  f.codRestrict (integralClosure R (I → K)) fun x ↦
    (Algebra.IsIntegral.isIntegral x).map f

/-- Normality of the base identifies integral rational functions coordinatewise. -/
theorem integralPiMap_bijective (R K I : Type*) [CommRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [IsIntegrallyClosed R] [Finite I] :
    Function.Bijective (integralPiMap R K I) := by
  constructor
  · intro f g h
    funext i
    apply IsFractionRing.injective R K
    exact congrArg (fun z : integralClosure R (I → K) ↦ (z : I → K) i) h
  · intro f
    have h (i : I) : ∃ r : R, algebraMap R K r = (f : I → K) i := by
      apply IsIntegrallyClosed.isIntegral_iff.mp
      exact f.property.map (Pi.evalAlgHom R (fun _ : I ↦ K) i)
    choose r hr using h
    exact ⟨r, by apply Subtype.ext; funext i; exact hr i⟩

/-- The integral closure in a finite product of fraction fields is the product of bases. -/
def integralPiEquiv (R K I : Type*) [CommRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [IsIntegrallyClosed R] [Finite I] :
    (I → R) ≃ₐ[R] integralClosure R (I → K) :=
  AlgEquiv.ofBijective (integralPiMap R K I) (integralPiMap_bijective R K I)

/-- The rational and integral scalar actions on constant generic functions agree. -/
instance constantGenericScalarTower :
    IsScalarTower ZInvTwo ℚ (constantPoints A).GenericCoordinateAlgebra :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The normalization of constant generic functions is the integral function algebra. -/
def constantIntegralCoordinateEquiv :
    integralClosure ZInvTwo (constantPoints A).GenericCoordinateAlgebra ≃ₐ[ZInvTwo]
      (A → ZInvTwo) :=
  (AlgEquiv.mapIntegralClosure ((constantGenericEquiv A).symm.restrictScalars ZInvTwo)).trans
    (integralPiEquiv ZInvTwo ℚ A).symm

/-- Evaluation of normalized coordinates agrees with generic evaluation. -/
theorem constantIntegralCoordinateEquiv_apply
    (f : integralClosure ZInvTwo (constantPoints A).GenericCoordinateAlgebra) (a : A) :
    algebraMap ZInvTwo (AlgebraicClosure ℚ) (constantIntegralCoordinateEquiv A f a) =
      (f : (constantPoints A).GenericCoordinateAlgebra) a := by
  let g := (constantGenericEquiv A).symm (f : (constantPoints A).GenericCoordinateAlgebra)
  have h := congrArg (fun z : integralClosure ZInvTwo (A → ℚ) ↦ (z : A → ℚ) a)
    ((integralPiEquiv ZInvTwo ℚ A).apply_symm_apply
      (AlgEquiv.mapIntegralClosure ((constantGenericEquiv A).symm.restrictScalars ZInvTwo) f))
  change algebraMap ZInvTwo ℚ (constantIntegralCoordinateEquiv A f a) = g a at h
  rw [IsScalarTower.algebraMap_apply ZInvTwo ℚ (AlgebraicClosure ℚ), h]
  exact congrArg (fun z : (constantPoints A).GenericCoordinateAlgebra ↦ z a)
    ((constantGenericEquiv A).apply_symm_apply f)

/-- The existing canonical constant model has the expected integral function algebra. -/
def constantCoordinateEquiv :
    (constantFiniteFlat A).model.CoordinateRing ≃ₐ[ZInvTwo] (A → ZInvTwo) :=
  constantIntegralCoordinateEquiv A

end ThreeAdicPlan
