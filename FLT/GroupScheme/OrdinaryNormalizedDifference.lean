/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.OrdinaryModelFiberPoints
public import FLT.GroupScheme.HopfPointFiberDifferenceEvaluation
public import FLT.GaloisRepresentation.Extensions.OrdinaryFiltrationBasis

/-!
# The quotient-normalized ordinary difference on integral coordinates

Evaluation of the Hom cocycle at one gives the beta-inverse normalized
vector difference. Integral evaluation identifies its injected vector with
the actual Hopf difference, without a comparison equality as an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open GaloisRepresentation.Extensions WithConv
namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

/-- Subtraction of original generic points is the antipode/convolution difference. -/
theorem FF.integralPoints_sub (X : FF R K) (x y : X.Points) :
    X.integralPoints (y - x) =
      (toConv ((X.integralPoints x).comp (HopfAlgebra.antipodeAlgHom R X.CoordinateRing)) *
        toConv (X.integralPoints y)).ofConv := by
  have h : toConv (X.integralPoints x) * toConv (X.integralPoints (y - x)) =
      toConv (X.integralPoints y) := by
    apply ofConv_injective
    ext a
    rw [AlgHom.convMul_apply]
    have he : x + (y - x) = y := by abel
    exact (AlgHom.congr_fun ((X.integralPoints_add x (y - x)).symm.trans
      (congrArg X.integralPoints he)) a)
  have hd := congrArg
    (toConv ((X.integralPoints x).comp (HopfAlgebra.antipodeAlgHom R X.CoordinateRing)) * ·) h
  rw [← mul_assoc, HopfAlgebra.conv_antipode_mul, one_mul] at hd
  exact congrArg ofConv hd

variable {k : Type} [Field k] (X : FF R K) [Module k X.Points]
  [SMulCommClass (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) k X.Points]
  [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace X.Points] [DiscreteTopology X.Points]
  {α β : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* kˣ}
  (E : OrdinaryFiltration (Representation.ofDistribMulAction k
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) X.Points) α β)
  (hρ : ∀ x : X.Points, Continuous (fun g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K ↦ g • x))

/-- The constructed Hom cocycle evaluates to the actual normalized integral Hopf difference. -/
theorem ordinary_cocycle_integralDifference (w : X.Points) (hw : E.projection w = 1)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    X.integralPoints (E.injection ((show k →ₗ[k] k from (E.cocycleOf hρ w hw).val g) 1)) =
      (toConv ((X.integralPoints w).comp (HopfAlgebra.antipodeAlgHom R X.CoordinateRing)) *
        toConv (X.integralPoints ((β g : k)⁻¹ • g • w))).ofConv := by
  rw [E.cocycleOf_spec]
  exact X.integralPoints_sub _ _

variable {B : Type} [CommRing B] [HopfAlgebra R B]
  [Algebra B X.CoordinateRing] [IsScalarTower R B X.CoordinateRing]

/-- The inverse-torsor difference is the injected normalized Hom coefficient
on middle coordinates, for the points corresponding to the two specified vectors. -/
theorem ordinary_pointFiberDifference_cocycle
    (f : B →ₐc[R] X.CoordinateRing)
    (hf : f.toAlgHom = IsScalarTower.toAlgHom R B X.CoordinateRing) (p : B →ₐ[R] R)
    (x y : HopfAlgebra.PointFiber (A := X.CoordinateRing) p →ₐ[R] AlgebraicClosure K)
    (w : X.Points) (hw : E.projection w = 1)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hx : x.comp (HopfAlgebra.pointFiberMap p) = X.integralPoints w)
    (hy : y.comp (HopfAlgebra.pointFiberMap p) =
      X.integralPoints ((β g : k)⁻¹ • g • w)) :
    (HopfAlgebra.pointFiberDifferenceEvaluation f hf p x y).comp
      (Ideal.Quotient.mkₐ R (HopfAlgebra.augmentationIdeal f)) =
        X.integralPoints (E.injection ((show k →ₗ[k] k from (E.cocycleOf hρ w hw).val g) 1)) := by
  rw [HopfAlgebra.pointFiberDifferenceEvaluation_map, hx, hy]
  exact (ordinary_cocycle_integralDifference X E hρ w hw g).symm

end ThreeAdicPlan
