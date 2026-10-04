/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCartierDual
public import FLT.GroupScheme.IntegralModelPoints
public import FLT.GroupScheme.RaynaudAugmentationRank

/-!
# Constant finite group models over a general integral base

The integral dual of the group algebra has the function algebra as coordinates.
Evaluation at group elements gives its actual geometric points, with trivial
Galois action. This construction does not invert the order of the group.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
open HopfAlgebra HopfAlgebra.CartierDual
namespace ThreeAdicPlan

variable (R K A : Type) [CommRing R] [Field K] [Algebra R K]
  [AddCommGroup A] [Finite A]

/-- The integral function Hopf algebra, constructed as a dual group algebra. -/
abbrev ConstantGroupCoordinate := CartierDual R (MonoidAlgebra R (Multiplicative A))

/-- The constant model uses the actual generic geometric points. -/
def constantGroupModel : FF R K := by
  let : Algebra.Etale R (ConstantGroupCoordinate R A) :=
    Algebra.Etale.of_equiv (groupAlgebraEquiv R (Multiplicative A)).symm
  exact FF.ofCoordinateRing (ConstantGroupCoordinate R A)

/-- The actual integral coordinate algebra is the finite function algebra. -/
def constantGroupCoordinates :
    (constantGroupModel R K A).CoordinateRing ≃ₐ[R] (Multiplicative A → R) :=
  groupAlgebraEquiv R (Multiplicative A)

/-- Evaluation at a group element is an integral point. -/
def constantGroupIntegralPoint (a : A) :
    (constantGroupModel R K A).CoordinateRing →ₐ[R] R :=
  (Pi.evalAlgHom R (fun _ : Multiplicative A ↦ R) (Multiplicative.ofAdd a)).comp
    (constantGroupCoordinates R K A).toAlgHom

/-- The geometric point obtained from this integral evaluation. -/
def constantGroupPoint (a : A) : (constantGroupModel R K A).Points :=
  (constantGroupModel R K A).integralPoints.symm
    ((Algebra.ofId R (AlgebraicClosure K)).comp (constantGroupIntegralPoint R K A a))

/-- Geometric evaluation retains the original integral evaluation. -/
@[simp] theorem constantGroupPoint_integral (a : A) :
    (constantGroupModel R K A).integralPoints (constantGroupPoint R K A a) =
      (Algebra.ofId R (AlgebraicClosure K)).comp (constantGroupIntegralPoint R K A a) :=
  Equiv.apply_symm_apply _ _

/-- Every constructed point is fixed by the original absolute Galois group. -/
theorem constantGroupPoint_fixed (a : A)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    g • constantGroupPoint R K A a = constantGroupPoint R K A a := by
  apply (constantGroupModel R K A).integralPoints.injective
  rw [FF.integralPoints_smul, constantGroupPoint_integral]
  ext φ
  exact g.commutes ((algebraMap R K) (constantGroupIntegralPoint R K A a φ))

/-- Tensor evaluation in the dual group algebra reads a pair of group elements. -/
theorem constantGroupPoint_tensor (a b : A)
    (t : ConstantGroupCoordinate R A ⊗[R] ConstantGroupCoordinate R A) :
    Algebra.TensorProduct.lift (constantGroupIntegralPoint R K A a)
      (constantGroupIntegralPoint R K A b) (fun _ _ ↦ .all ..) t =
      tensorEquiv R (MonoidAlgebra R (Multiplicative A)) (MonoidAlgebra R (Multiplicative A)) t
        (MonoidAlgebra.single (Multiplicative.ofAdd a) 1 ⊗ₜ[R]
          MonoidAlgebra.single (Multiplicative.ofAdd b) 1) := by
  induction t using TensorProduct.inductionOn with
  | tmul φ ψ =>
    simp only [Algebra.TensorProduct.lift_tmul, tensorEquiv_tmul]
    rfl
  | add t s ht hs => simp only [map_add, LinearMap.add_apply, ht, hs]

/-- Convolution of the actual evaluations is addition in the constant group. -/
theorem constantGroupPoint_add (a b : A) :
    constantGroupPoint R K A (a + b) = constantGroupPoint R K A a + constantGroupPoint R K A b := by
  apply (constantGroupModel R K A).integralPoints.injective
  rw [FF.integralPoints_add, constantGroupPoint_integral, constantGroupPoint_integral,
    constantGroupPoint_integral]
  ext φ
  change algebraMap R (AlgebraicClosure K) (constantGroupIntegralPoint R K A (a + b) φ) = _
  have ht (t : ConstantGroupCoordinate R A ⊗[R] ConstantGroupCoordinate R A) :
      Algebra.TensorProduct.lift
        ((Algebra.ofId R (AlgebraicClosure K)).comp (constantGroupIntegralPoint R K A a))
        ((Algebra.ofId R (AlgebraicClosure K)).comp (constantGroupIntegralPoint R K A b))
        (fun _ _ ↦ .all ..) t =
      algebraMap R (AlgebraicClosure K)
        (Algebra.TensorProduct.lift (constantGroupIntegralPoint R K A a)
          (constantGroupIntegralPoint R K A b) (fun _ _ ↦ .all ..) t) := by
    induction t using TensorProduct.inductionOn with
    | tmul φ ψ => exact (map_mul (algebraMap R _) _ _).symm
    | add t s ht hs => simp only [map_add, ht, hs]
  rw [AlgHom.comp_apply, ht, constantGroupPoint_tensor]
  congr 1
  change _ = tensorEquiv R _ _ (comul φ) _
  rw [comul_eval, MonoidAlgebra.single_mul_single, one_mul]
  rfl

end ThreeAdicPlan
