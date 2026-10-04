/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.IntegralModelPoints
public import FLT.GroupScheme.OrdinaryFiltrationModels
public import FLT.GroupScheme.HopfPointFiberPoints

/-!
# The actual integral ordinary fibre and its generic points

The equivalence is derived from tensor restriction and the constructed integral
quotient. It does not assume a multiplicative classification of the kernel.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open GaloisRepresentation.Extensions WithConv HopfAlgebra
namespace ThreeAdicPlan

variable {R K k : Type} [CommRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]
  [IsPrincipalIdealRing R] [Field k]
  (X : FF R K) [Module k X.Points]
  [SMulCommClass (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) k X.Points]
  {α β : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* kˣ}
  (E : OrdinaryFiltration (Representation.ofDistribMulAction k
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) X.Points) α β)

/-- Integral evaluation of the ordinary quotient is the original projection. -/
theorem ordinary_integralPoints_projection (x : X.Points) :
    (ordinaryQuotientModel X E).integralPoints (E.projection x) =
      (X.integralPoints x).comp (ordinaryModelExtension X E).quotient.toAlgHom := by
  rw [← ordinaryModelExtension_quotient X E x]
  exact integralPoints_genericHom (X := X) (Y := ordinaryQuotientModel X E) _ x

/-- Integral evaluation of the kernel inclusion is the original injection. -/
theorem ordinary_integralPoints_injection (a : k) :
    X.integralPoints (E.injection a) =
      ((ordinaryKernelModel X E).integralPoints a).comp
        (ordinaryModelExtension X E).inclusion.toAlgHom := by
  rw [← ordinaryModelExtension_inclusion X E a]
  exact integralPoints_genericHom (X := ordinaryKernelModel X E) (Y := X) _ a

/-- Points above a quotient vector, on the actual integral coordinate algebras. -/
def ordinaryIntegralFiberEquiv (a : k) :
    {x : X.Points // E.projection x = a} ≃
      FiberPoints (ordinaryModelExtension X E).quotient
        (toConv ((ordinaryQuotientModel X E).integralPoints a)) where
  toFun x := ⟨toConv (X.integralPoints x.val), by
    apply ofConv_injective
    exact (ordinary_integralPoints_projection X E x.val).symm.trans
      (congrArg (ordinaryQuotientModel X E).integralPoints x.property)⟩
  invFun x := ⟨X.integralPoints.symm x.val.ofConv, by
    apply (ordinaryQuotientModel X E).integralPoints.injective
    rw [ordinary_integralPoints_projection, Equiv.apply_symm_apply]
    exact congrArg ofConv x.property⟩
  left_inv x := by apply Subtype.ext; exact X.integralPoints.symm_apply_apply x.val
  right_inv x := by
    apply Subtype.ext
    exact congrArg toConv (X.integralPoints.apply_symm_apply x.val.ofConv)

/-- The quotient morphism supplies the integral coordinate algebra structure. -/
local instance ordinaryFiberCoordinateAlgebra :
    Algebra (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  (ordinaryModelExtension X E).quotient.toAlgHom.toRingHom.toAlgebra
/-- The quotient algebra structure respects the original base ring. -/
local instance ordinaryFiberCoordinateTower :
    IsScalarTower R (ordinaryQuotientModel X E).CoordinateRing X.CoordinateRing :=
  IsScalarTower.of_algebraMap_eq'
    (ordinaryModelExtension X E).quotient.toAlgHom.comp_algebraMap.symm

/-- The tensor-product fibre at an integral point has the specified generic vectors. -/
def ordinaryPointFiberEquiv (p : (ordinaryQuotientModel X E).CoordinateRing →ₐ[R] R) :
    (PointFiber (A := X.CoordinateRing) p →ₐ[R] AlgebraicClosure K) ≃
      {x : X.Points // E.projection x =
        (ordinaryQuotientModel X E).integralPoints.symm ((Algebra.ofId R _).comp p)} := by
  let a := (ordinaryQuotientModel X E).integralPoints.symm ((Algebra.ofId R _).comp p)
  have e := ordinaryIntegralFiberEquiv X E a
  dsimp only [a] at e
  rw [Equiv.apply_symm_apply] at e
  exact (pointFiberPointsEquiv (ordinaryModelExtension X E).quotient (by rfl) p).trans e.symm

end ThreeAdicPlan
