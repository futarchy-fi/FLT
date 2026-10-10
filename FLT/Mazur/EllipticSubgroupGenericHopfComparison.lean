/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupGenericConstantCoordinates

/-!
# The actual generic closure is the constant subgroup as a Hopf algebra

The original interpolation equivalence preserves the counit and
comultiplication, using the proved integral evaluation identities.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open HopfAlgebra HopfAlgebra.CartierDual

namespace FLT.Mazur.EllipticSubgroupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) [Finite H]
  [IsDedekindDomain A] (hΔ : IsUnit W.Δ)

/-- The original integral counit is the constant generic counit after inclusion. -/
theorem globalClosureConstantInclusion_counit (a : GlobalClosure A W H) :
    letI := globalClosureHopfAlgebra A W H hΔ
    algebraMap A K (Coalgebra.counit (R := A) a) =
      Coalgebra.counit (R := K) (globalClosureConstantInclusion A W H a) := by
  let _ := globalClosureHopfAlgebra A W H hΔ
  rw [ConstantGroupTensorEvaluation.counit_evaluation]
  change _ = ConstantGroupTensorEvaluation.evaluation K (Multiplicative H)
    (Multiplicative.ofAdd 0) (globalClosureConstantInclusion A W H a)
  rw [globalClosureConstantInclusion_evaluation]
  exact congrArg (algebraMap A K)
    (AlgHom.congr_fun (globalClosureHopf_counit_eq_evaluation A W H hΔ) a)

/-- The scalar tensor comparison retains evaluation at each original subgroup pair. -/
theorem globalClosureConstantInclusion_tensor (P Q : H)
    (t : GlobalClosure A W H ⊗[A] GlobalClosure A W H) :
    letI := globalClosureHopfAlgebra A W H hΔ
    Algebra.TensorProduct.productMap
      (ConstantGroupTensorEvaluation.evaluation K (Multiplicative H) (Multiplicative.ofAdd P))
      (ConstantGroupTensorEvaluation.evaluation K (Multiplicative H) (Multiplicative.ofAdd Q))
      (ThreeAdicPlan.bialgebraScalarTensorMap A K (GlobalClosure A W H)
        (CartierDual K (MonoidAlgebra K (Multiplicative H)))
          (globalClosureConstantInclusion A W H) t) =
      algebraMap A K (globalClosureTensorEvaluation A W H P Q t) := by
  let _ := globalClosureHopfAlgebra A W H hΔ
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [ThreeAdicPlan.bialgebraScalarTensorMap, Algebra.TensorProduct.lift_tmul,
      AlgHom.comp_apply, AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one, Algebra.TensorProduct.productMap_apply_tmul,
      globalClosureConstantInclusion_evaluation, globalClosureTensorEvaluation_tmul, map_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The actual comultiplication agrees with the constant generic comultiplication. -/
theorem globalClosureConstantInclusion_comul (a : GlobalClosure A W H) :
    letI := globalClosureHopfAlgebra A W H hΔ
    ThreeAdicPlan.bialgebraScalarTensorMap A K (GlobalClosure A W H)
      (CartierDual K (MonoidAlgebra K (Multiplicative H)))
        (globalClosureConstantInclusion A W H) (Coalgebra.comul (R := A) a) =
      Coalgebra.comul (R := K) (globalClosureConstantInclusion A W H a) := by
  let _ := globalClosureHopfAlgebra A W H hΔ
  apply ConstantGroupTensorEvaluation.tensor_ext
  intro P Q
  change Algebra.TensorProduct.productMap
    (ConstantGroupTensorEvaluation.evaluation K (Multiplicative H)
      (Multiplicative.ofAdd P.toAdd))
    (ConstantGroupTensorEvaluation.evaluation K (Multiplicative H)
      (Multiplicative.ofAdd Q.toAdd)) _ = _
  rw [globalClosureConstantInclusion_tensor, ConstantGroupTensorEvaluation.comul_evaluation]
  change _ = ConstantGroupTensorEvaluation.evaluation K (Multiplicative H)
    (Multiplicative.ofAdd (P.toAdd + Q.toAdd)) (globalClosureConstantInclusion A W H a)
  rw [globalClosureConstantInclusion_evaluation]
  exact congrArg (algebraMap A K)
    (AlgHom.congr_fun (globalClosureHopf_comul_evaluation A W H hΔ P.toAdd Q.toAdd) a)

/-- The original generic comparison is an equivalence preserving all bialgebra operations. -/
def globalClosureGenericHopfEquiv :
    letI := globalClosureHopfAlgebra A W H hΔ
    K ⊗[A] GlobalClosure A W H ≃ₐc[K] CartierDual K (MonoidAlgebra K (Multiplicative H)) := by
  letI := globalClosureHopfAlgebra A W H hΔ
  exact ThreeAdicPlan.bialgebraScalarExtensionEquiv A K (GlobalClosure A W H)
    (CartierDual K (MonoidAlgebra K (Multiplicative H)))
    (globalClosureConstantInclusion A W H) (globalClosureGenericConstantEquiv A W H)
    (globalClosureGenericConstantEquiv_one_tmul A W H)
    (globalClosureConstantInclusion_counit A W H hΔ)
    (globalClosureConstantInclusion_comul A W H hΔ)

end FLT.Mazur.EllipticSubgroupChart
