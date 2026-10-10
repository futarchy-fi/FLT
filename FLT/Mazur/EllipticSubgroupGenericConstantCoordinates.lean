/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupHopfMultiplication
public import FLT.Mazur.ConstantGroupTensorEvaluation
public import FLT.GroupScheme.BialgebraBaseChange

/-!
# The generic closure comparison in constant group coordinates

The existing interpolation equivalence is expressed in the dual group algebra.
Its point evaluations remain the original integral subgroup evaluations.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open HopfAlgebra HopfAlgebra.CartierDual

namespace FLT.Mazur.EllipticSubgroupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) [Finite H]

/-- The existing generic algebra comparison, with the constant Hopf coordinates as target. -/
def globalClosureGenericConstantEquiv : K ⊗[A] GlobalClosure A W H ≃ₐ[K]
    CartierDual K (MonoidAlgebra K (Multiplicative H)) :=
  (globalClosureGenericEquiv A W H).trans (groupAlgebraEquiv K (Multiplicative H)).symm

/-- The original integral coordinates embedded in the generic constant Hopf algebra. -/
def globalClosureConstantInclusion : GlobalClosure A W H →ₐ[A]
    CartierDual K (MonoidAlgebra K (Multiplicative H)) :=
  ((groupAlgebraEquiv K (Multiplicative H)).symm.toAlgHom.restrictScalars A).comp
    (globalClosureGenericInclusion A W H)

/-- The generic constant comparison extends the actual integral coordinate inclusion. -/
theorem globalClosureGenericConstantEquiv_one_tmul (a : GlobalClosure A W H) :
    globalClosureGenericConstantEquiv A W H (1 ⊗ₜ[A] a) =
      globalClosureConstantInclusion A W H a := by
  change (groupAlgebraEquiv K (Multiplicative H)).symm
    (globalClosureGenericMap A W H (1 ⊗ₜ[A] a)) = _
  rw [globalClosureGenericMap_one_tmul]
  rfl

omit [Finite H] in
/-- Each constant coordinate evaluation is the original integral evaluation in the field. -/
theorem globalClosureConstantInclusion_evaluation (P : H) (a : GlobalClosure A W H) :
    ConstantGroupTensorEvaluation.evaluation K (Multiplicative H) (Multiplicative.ofAdd P)
      (globalClosureConstantInclusion A W H a) =
        algebraMap A K (globalClosureEvaluation A W H P a) :=
  congrFun ((groupAlgebraEquiv K (Multiplicative H)).apply_symm_apply
    (globalClosureGenericInclusion A W H a)) P

/-- All original generic point evaluations are retained by the algebra equivalence. -/
theorem globalClosureGenericConstantEquiv_evaluation
    (P : H) (x : K ⊗[A] GlobalClosure A W H) :
    ConstantGroupTensorEvaluation.evaluation K (Multiplicative H) (Multiplicative.ofAdd P)
      (globalClosureGenericConstantEquiv A W H x) = globalClosureGenericEquiv A W H x P :=
  congrFun ((groupAlgebraEquiv K (Multiplicative H)).apply_symm_apply
    (globalClosureGenericEquiv A W H x)) P

end FLT.Mazur.EllipticSubgroupChart
