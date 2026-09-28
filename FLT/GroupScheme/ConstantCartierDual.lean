/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantCoordinates

/-!
# Cartier duals of diagonalizable groups are the canonical constant models

The integral function-algebra comparison respects counits and
comultiplication. In particular the dual of the cube-root group is
identified with the repository's existing constant-three Hopf model.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

open HopfAlgebra.CartierDual

variable (A : Type) [AddCommGroup A] [Finite A]

/-- The canonical constant normalization is étale over the integral base. -/
local instance : Algebra.Etale ZInvTwo
    (integralClosure ZInvTwo (constantPoints A).GenericCoordinateAlgebra) :=
  (constantEtaleModel A).etale

local notation "C" => integralClosure ZInvTwo
  (FiniteContinuousGaloisModule.GenericCoordinateAlgebra (constantPoints A))

/-- The canonical integral Hopf structure on constant coordinates. -/
local instance : HopfAlgebra ZInvTwo C :=
  integralClosureHopfAlgebra ZInvTwo ℚ (constantPoints A).GenericCoordinateAlgebra

/-- The constant coordinate algebra is the integral dual group algebra. -/
def constantDiagonalDualAlgEquiv :
    C ≃ₐ[ZInvTwo]
      HopfAlgebra.CartierDual ZInvTwo (MonoidAlgebra ZInvTwo (Multiplicative A)) :=
  (constantIntegralCoordinateEquiv A).trans
    ((AlgEquiv.piCongrLeft ZInvTwo (fun _ : A ↦ ZInvTwo) Multiplicative.toAdd).trans
      (groupAlgebraEquiv ZInvTwo (Multiplicative A)).symm)

/-- The dual functional evaluates basis elements by the constant integral function. -/
@[simp] theorem constantDiagonalDualAlgEquiv_apply
    (f : C) (a : Multiplicative A) :
    constantDiagonalDualAlgEquiv A f (MonoidAlgebra.single a 1) =
      constantIntegralCoordinateEquiv A f a.toAdd := by
  exact congrFun ((groupAlgebraEquiv ZInvTwo (Multiplicative A)).apply_symm_apply
    ((AlgEquiv.piCongrLeft ZInvTwo (fun _ : A ↦ ZInvTwo) Multiplicative.toAdd)
      (constantIntegralCoordinateEquiv A f))) a

private theorem integralMap_injective :
    Function.Injective (algebraMap ZInvTwo (AlgebraicClosure ℚ)) := by
  rw [IsScalarTower.algebraMap_eq ZInvTwo ℚ (AlgebraicClosure ℚ)]
  exact (algebraMap ℚ (AlgebraicClosure ℚ)).injective.comp (IsFractionRing.injective ZInvTwo ℚ)

private theorem constantDualTensor_eval
    (z : C ⊗[ZInvTwo]
      C) (a b : Multiplicative A) :
    algebraMap ZInvTwo (AlgebraicClosure ℚ)
      (tensorEquiv ZInvTwo (MonoidAlgebra ZInvTwo (Multiplicative A))
        (MonoidAlgebra ZInvTwo (Multiplicative A))
        (TensorProduct.map (constantDiagonalDualAlgEquiv A).toLinearMap
          (constantDiagonalDualAlgEquiv A).toLinearMap z)
        (MonoidAlgebra.single a 1 ⊗ₜ MonoidAlgebra.single b 1)) =
      GaloisModule.tensorEquiv ℚ (AlgebraicClosure ℚ) (constantPoints A) (constantPoints A)
        (integralTensorMap ZInvTwo ℚ (constantPoints A).GenericCoordinateAlgebra z)
        (a.toAdd, b.toAdd) := by
  induction z using TensorProduct.inductionOn with
  | tmul f g =>
    simp only [TensorProduct.map_tmul, AlgEquiv.toLinearMap_apply, tensorEquiv_tmul,
      constantDiagonalDualAlgEquiv_apply, map_mul,
      integralTensorMap_tmul]
    change _ = (f : (constantPoints A).GenericCoordinateAlgebra) a.toAdd *
      (g : (constantPoints A).GenericCoordinateAlgebra) b.toAdd
    rw [constantIntegralCoordinateEquiv_apply, constantIntegralCoordinateEquiv_apply]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply]
    exact congrArg₂ (· + ·) hx hy

/-- The coordinate identification preserves the integral counit. -/
theorem constantDiagonalDual_counit (f : C) :
    Coalgebra.counit (R := ZInvTwo) (constantDiagonalDualAlgEquiv A f) =
      Coalgebra.counit (R := ZInvTwo) f := by
  apply integralMap_injective
  change algebraMap ZInvTwo (AlgebraicClosure ℚ)
    (constantDiagonalDualAlgEquiv A f (MonoidAlgebra.single 1 1)) =
      algebraMap ZInvTwo (AlgebraicClosure ℚ)
        (integralClosureCounit ZInvTwo ℚ (constantPoints A).GenericCoordinateAlgebra
          (Bialgebra.counitAlgHom ℚ (constantPoints A).GenericCoordinateAlgebra) f)
  rw [constantDiagonalDualAlgEquiv_apply, constantIntegralCoordinateEquiv_apply,
    IsScalarTower.algebraMap_apply ZInvTwo ℚ (AlgebraicClosure ℚ),
    algebraMap_integralClosureCounit]
  exact (GaloisModule.GenericFiber.algebraMap_counitAlgHom ℚ
    (AlgebraicClosure ℚ) (constantPoints A) f).symm

/-- The coordinate identification preserves integral comultiplication. -/
theorem constantDiagonalDual_comul (f : C) :
    TensorProduct.map (constantDiagonalDualAlgEquiv A).toLinearMap
      (constantDiagonalDualAlgEquiv A).toLinearMap (Coalgebra.comul (R := ZInvTwo) f) =
        Coalgebra.comul (R := ZInvTwo) (constantDiagonalDualAlgEquiv A f) := by
  apply (tensorEquiv ZInvTwo (MonoidAlgebra ZInvTwo (Multiplicative A))
    (MonoidAlgebra ZInvTwo (Multiplicative A))).injective
  apply ((MonoidAlgebra.basis (Multiplicative A) ZInvTwo).tensorProduct
    (MonoidAlgebra.basis (Multiplicative A) ZInvTwo)).ext
  rintro ⟨a, b⟩
  simp only [Module.Basis.tensorProduct_apply, MonoidAlgebra.basis_apply]
  change tensorEquiv ZInvTwo (MonoidAlgebra ZInvTwo (Multiplicative A))
    (MonoidAlgebra ZInvTwo (Multiplicative A))
    (TensorProduct.map (constantDiagonalDualAlgEquiv A).toLinearMap
      (constantDiagonalDualAlgEquiv A).toLinearMap (Coalgebra.comul (R := ZInvTwo) f))
      (MonoidAlgebra.single a 1 ⊗ₜ MonoidAlgebra.single b 1) =
    tensorEquiv ZInvTwo (MonoidAlgebra ZInvTwo (Multiplicative A))
      (MonoidAlgebra ZInvTwo (Multiplicative A)) (comul (constantDiagonalDualAlgEquiv A f))
      (MonoidAlgebra.single a 1 ⊗ₜ MonoidAlgebra.single b 1)
  rw [comul_eval]
  apply integralMap_injective
  rw [constantDualTensor_eval]
  change GaloisModule.tensorEquiv ℚ (AlgebraicClosure ℚ) (constantPoints A) (constantPoints A)
    (integralTensorMap ZInvTwo ℚ (constantPoints A).GenericCoordinateAlgebra
      (integralComul ZInvTwo ℚ (constantPoints A).GenericCoordinateAlgebra f))
    (a.toAdd, b.toAdd) = _
  rw [integralTensorMap_comul]
  calc
    _ = (f : (constantPoints A).GenericCoordinateAlgebra) (a.toAdd + b.toAdd) :=
      GaloisModule.GenericFiber.comulAlgHom_eval ℚ (AlgebraicClosure ℚ)
        (constantPoints A) f a.toAdd b.toAdd
    _ = _ := by
      rw [MonoidAlgebra.single_mul_single, one_mul]
      change _ = algebraMap ZInvTwo (AlgebraicClosure ℚ)
        (constantDiagonalDualAlgEquiv A f (MonoidAlgebra.single (a * b) 1))
      rw [constantDiagonalDualAlgEquiv_apply, constantIntegralCoordinateEquiv_apply]
      rfl

/-- Integral Cartier duality identifies a diagonalizable model with the
canonical constant model on its character group. -/
def diagonalizableCartierDualEquiv :
    (diagonalizableFiniteFlat A).cartierDual.model.CoordinateRing ≃ₐc[ZInvTwo]
      (constantFiniteFlat A).model.CoordinateRing :=
  (BialgEquiv.ofAlgEquiv (constantDiagonalDualAlgEquiv A)
    (by ext f; exact constantDiagonalDual_counit A f)
    (by ext f : 1; exact constantDiagonalDual_comul A f)).symm

/-- The integral Cartier dual of the cube-root group is the existing constant-three model. -/
def muThreeCartierDualEquiv :
    muThree.cartierDual.model.CoordinateRing ≃ₐc[ZInvTwo] constantThree.model.CoordinateRing :=
  diagonalizableCartierDualEquiv (ZMod 3)

end ThreeAdicPlan
