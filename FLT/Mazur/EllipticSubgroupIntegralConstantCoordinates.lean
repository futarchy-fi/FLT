/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupGenericHopfComparison

/-!
# Integral comparison with constant subgroup coordinates

The original integral evaluations define a map to the constant Hopf algebra.
Its coalgebra laws follow from the actual addition and identity of the closure.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open HopfAlgebra HopfAlgebra.CartierDual

namespace FLT.Mazur.EllipticSubgroupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) [Finite H]

/-- Integral subgroup evaluation expressed in the constant dual group algebra. -/
def globalClosureIntegralConstantMap : GlobalClosure A W H →ₐ[A]
    CartierDual A (MonoidAlgebra A (Multiplicative H)) :=
  (groupAlgebraEquiv A (Multiplicative H)).symm.toAlgHom.comp
    (globalClosureEvaluations A W H)

omit [Finite H] in
/-- The comparison retains each original integral section. -/
theorem globalClosureIntegralConstantMap_evaluation (P : H) (a : GlobalClosure A W H) :
    ConstantGroupTensorEvaluation.evaluation A (Multiplicative H) (Multiplicative.ofAdd P)
      (globalClosureIntegralConstantMap A W H a) = globalClosureEvaluation A W H P a :=
  congrFun ((groupAlgebraEquiv A (Multiplicative H)).apply_symm_apply
    (globalClosureEvaluations A W H a)) P

/-- Integral constant coordinates still detect all original global functions. -/
theorem globalClosureIntegralConstantMap_injective :
    Function.Injective (globalClosureIntegralConstantMap A W H) :=
  (groupAlgebraEquiv A (Multiplicative H)).symm.injective.comp
    (globalClosureEvaluations_injective A W H)

omit [Finite H] in
/-- Tensor evaluation after the comparison is the original pair evaluation. -/
theorem globalClosureIntegralConstantMap_tensor (P Q : H)
    (t : GlobalClosure A W H ⊗[A] GlobalClosure A W H) :
    Algebra.TensorProduct.productMap
      (ConstantGroupTensorEvaluation.evaluation A (Multiplicative H) (Multiplicative.ofAdd P))
      (ConstantGroupTensorEvaluation.evaluation A (Multiplicative H) (Multiplicative.ofAdd Q))
      (Algebra.TensorProduct.map (globalClosureIntegralConstantMap A W H)
        (globalClosureIntegralConstantMap A W H) t) =
        globalClosureTensorEvaluation A W H P Q t := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.productMap_apply_tmul,
      globalClosureIntegralConstantMap_evaluation, globalClosureTensorEvaluation_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

variable [IsDedekindDomain A] (hΔ : IsUnit W.Δ)

/-- The original integral comparison preserves counit. -/
theorem globalClosureIntegralConstantMap_counit (a : GlobalClosure A W H) :
    letI := globalClosureHopfAlgebra A W H hΔ
    Coalgebra.counit (R := A) (globalClosureIntegralConstantMap A W H a) =
      Coalgebra.counit (R := A) a := by
  let _ := globalClosureHopfAlgebra A W H hΔ
  rw [ConstantGroupTensorEvaluation.counit_evaluation]
  change ConstantGroupTensorEvaluation.evaluation A (Multiplicative H)
    (Multiplicative.ofAdd 0) (globalClosureIntegralConstantMap A W H a) = _
  rw [globalClosureIntegralConstantMap_evaluation]
  exact (AlgHom.congr_fun (globalClosureHopf_counit_eq_evaluation A W H hΔ) a).symm

/-- The original integral comparison preserves comultiplication. -/
theorem globalClosureIntegralConstantMap_comul (a : GlobalClosure A W H) :
    letI := globalClosureHopfAlgebra A W H hΔ
    Algebra.TensorProduct.map (globalClosureIntegralConstantMap A W H)
      (globalClosureIntegralConstantMap A W H) (Coalgebra.comul (R := A) a) =
      Coalgebra.comul (R := A) (globalClosureIntegralConstantMap A W H a) := by
  let _ := globalClosureHopfAlgebra A W H hΔ
  apply ConstantGroupTensorEvaluation.tensor_ext
  intro P Q
  change Algebra.TensorProduct.productMap
    (ConstantGroupTensorEvaluation.evaluation A (Multiplicative H)
      (Multiplicative.ofAdd P.toAdd))
    (ConstantGroupTensorEvaluation.evaluation A (Multiplicative H)
      (Multiplicative.ofAdd Q.toAdd)) _ = _
  rw [globalClosureIntegralConstantMap_tensor, ConstantGroupTensorEvaluation.comul_evaluation]
  change _ = ConstantGroupTensorEvaluation.evaluation A (Multiplicative H)
    (Multiplicative.ofAdd (P.toAdd + Q.toAdd)) (globalClosureIntegralConstantMap A W H a)
  rw [globalClosureIntegralConstantMap_evaluation]
  exact AlgHom.congr_fun (globalClosureHopf_comul_evaluation A W H hΔ P.toAdd Q.toAdd) a

/-- The actual integral evaluations form a bialgebra homomorphism. -/
def globalClosureIntegralConstantHopfMap :
    letI := globalClosureHopfAlgebra A W H hΔ
    GlobalClosure A W H →ₐc[A] CartierDual A (MonoidAlgebra A (Multiplicative H)) := by
  letI := globalClosureHopfAlgebra A W H hΔ
  refine BialgHom.ofAlgHom (R := A) (A := GlobalClosure A W H)
    (B := CartierDual A (MonoidAlgebra A (Multiplicative H)))
    (globalClosureIntegralConstantMap A W H) ?_ ?_
  · apply AlgHom.ext
    intro a
    exact globalClosureIntegralConstantMap_counit A W H hΔ a
  · apply AlgHom.ext
    intro a
    exact globalClosureIntegralConstantMap_comul A W H hΔ a

end FLT.Mazur.EllipticSubgroupChart
