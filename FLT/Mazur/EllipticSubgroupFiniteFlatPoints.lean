/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupFiniteFlatModel
public import FLT.Mazur.EllipticSubgroupHopfSpecialization
public import FLT.GroupScheme.FiniteFlatDifferentials
public import FLT.GroupScheme.IntegralModelPoints
public import FLT.GroupScheme.RaynaudAugmentationRank

/-!
# Original subgroup points exhaust the finite-flat model

The integral evaluations give an additive, Galois-fixed copy of the original
subgroup in the geometric points. Equality of ranks proves it is the entire
point group, retaining the original coordinates and every torsion relation.
-/

@[expose] public noncomputable section

open HopfAlgebra

namespace FLT.Mazur.EllipticSubgroupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] globalClosureGenericHopfEquiv

variable {K : Type} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) [Finite H]
  [IsDedekindDomain A] (hΔ : IsUnit W.Δ)

/-- The geometric point given by an original integral subgroup evaluation. -/
def globalClosureFiniteFlatPoint (P : H) : (globalClosureFiniteFlatModel A W H hΔ).Points :=
  (globalClosureFiniteFlatModel A W H hΔ).integralPoints.symm
    (globalClosureSpecializedEvaluation A W H (AlgebraicClosure K) P)

/-- This geometric point restricts to precisely the original integral evaluation. -/
@[simp] theorem globalClosureFiniteFlatPoint_integral (P : H) :
    (globalClosureFiniteFlatModel A W H hΔ).integralPoints
      (globalClosureFiniteFlatPoint A W H hΔ P) =
        globalClosureSpecializedEvaluation A W H (AlgebraicClosure K) P :=
  Equiv.apply_symm_apply _ _

/-- The original subgroup addition is the addition of its actual model points. -/
theorem globalClosureFiniteFlatPoint_add (P Q : H) :
    globalClosureFiniteFlatPoint A W H hΔ (P + Q) =
      globalClosureFiniteFlatPoint A W H hΔ P + globalClosureFiniteFlatPoint A W H hΔ Q := by
  let _ := globalClosureHopfAlgebra A W H hΔ
  apply (globalClosureFiniteFlatModel A W H hΔ).integralPoints.injective
  rw [ThreeAdicPlan.FF.integralPoints_add, globalClosureFiniteFlatPoint_integral,
    globalClosureFiniteFlatPoint_integral, globalClosureFiniteFlatPoint_integral]
  apply AlgHom.ext
  intro a
  change algebraMap A (AlgebraicClosure K) (globalClosureEvaluation A W H (P + Q) a) =
    Algebra.TensorProduct.productMap
      (globalClosureSpecializedEvaluation A W H (AlgebraicClosure K) P)
      (globalClosureSpecializedEvaluation A W H (AlgebraicClosure K) Q)
      (Coalgebra.comul (R := A) a)
  rw [globalClosureSpecializedEvaluation_tensor]
  exact congrArg (algebraMap A (AlgebraicClosure K))
    (AlgHom.congr_fun (globalClosureHopf_comul_evaluation A W H hΔ P Q) a).symm

/-- Distinct original subgroup points remain distinct geometric points of the model. -/
theorem globalClosureFiniteFlatPoint_injective :
    Function.Injective (globalClosureFiniteFlatPoint A W H hΔ) := by
  intro P Q h
  apply globalClosureEvaluation_injective A W H
  apply AlgHom.ext
  intro a
  have he := congrArg (globalClosureFiniteFlatModel A W H hΔ).integralPoints h
  rw [globalClosureFiniteFlatPoint_integral, globalClosureFiniteFlatPoint_integral] at he
  exact ((algebraMap K (AlgebraicClosure K)).injective.comp
    (IsFractionRing.injective A K)) (AlgHom.congr_fun he a)

/-- Every original point is fixed by the actual generic absolute Galois action. -/
theorem globalClosureFiniteFlatPoint_fixed (P : H)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    g • globalClosureFiniteFlatPoint A W H hΔ P = globalClosureFiniteFlatPoint A W H hΔ P := by
  apply (globalClosureFiniteFlatModel A W H hΔ).integralPoints.injective
  rw [ThreeAdicPlan.FF.integralPoints_smul, globalClosureFiniteFlatPoint_integral]
  ext a
  exact g.commutes (algebraMap A K (globalClosureEvaluation A W H P a))

variable [PerfectField K]

/-- The point group of the actual model has exactly the original subgroup cardinality. -/
theorem globalClosureFiniteFlatModel_card :
    Nat.card (globalClosureFiniteFlatModel A W H hΔ).Points = Nat.card H := by
  rw [← ThreeAdicPlan.FF.coordinate_finrank]
  exact globalClosure_finrank A W H

/-- The constructed original points exhaust the model's geometric generic fiber. -/
theorem globalClosureFiniteFlatPoint_bijective :
    Function.Bijective (globalClosureFiniteFlatPoint A W H hΔ) :=
  (Nat.bijective_iff_injective_and_card _).mpr
    ⟨globalClosureFiniteFlatPoint_injective A W H hΔ,
      (globalClosureFiniteFlatModel_card A W H hΔ).symm⟩

/-- The original subgroup is the actual full geometric generic point group. -/
def globalClosureFiniteFlatPointEquiv : H ≃+ (globalClosureFiniteFlatModel A W H hΔ).Points :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' _ (globalClosureFiniteFlatPoint_add A W H hΔ))
    (globalClosureFiniteFlatPoint_bijective A W H hΔ)

/-- Every original torsion relation holds on the entire model point group. -/
theorem globalClosureFiniteFlatModel_killedBy (n : ℕ) (hn : ∀ P : H, n • P = 0) :
    ThreeAdicPlan.KilledBy n (globalClosureFiniteFlatModel A W H hΔ) := by
  intro x
  obtain ⟨P, rfl⟩ := (globalClosureFiniteFlatPointEquiv A W H hΔ).surjective x
  rw [← map_nsmul, hn, map_zero]

end FLT.Mazur.EllipticSubgroupChart
