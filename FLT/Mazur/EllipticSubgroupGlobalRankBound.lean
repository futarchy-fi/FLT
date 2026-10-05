/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupGlobalEvaluation

/-!
# A rank bound from the actual subgroup sections

Global evaluation embeds the integral coordinate module into one copy of the
base for each subgroup point. Scalar extension embeds its generic fiber into
the split point algebra. Surjectivity of that generic map remains a separate step.
-/

@[expose] public noncomputable section

open scoped TensorProduct nonZeroDivisors

namespace FLT.Mazur.EllipticSubgroupChart

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) [Finite H]

/-- The actual global coordinate rank is at most the subgroup cardinality. -/
theorem globalClosure_finrank_le_card :
    Module.finrank A (GlobalClosure A W H) ≤ Nat.card H := by
  classical
  let _ := Fintype.ofFinite H
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := (globalClosureEvaluations A W H).toLinearMap)
    (globalClosureEvaluations_injective A W H)
  simpa only [Module.finrank_pi, Nat.card_eq_fintype_card] using h

/-- Global functions evaluated at the actual generic subgroup points. -/
def globalClosureGenericInclusion : GlobalClosure A W H →ₐ[A] (H → K) :=
  AlgHom.pi fun P => (Algebra.ofId A K).comp (globalClosureEvaluation A W H P)

/-- Integral global evaluation remains injective after embedding its values in the field. -/
theorem globalClosureGenericInclusion_injective :
    Function.Injective (globalClosureGenericInclusion A W H) := by
  intro a b hab
  apply globalClosureEvaluations_injective A W H
  funext P
  exact Subtype.coe_injective (congrFun hab P)

/-- Scalar extension of the actual global point evaluation map. -/
def globalClosureGenericMap : K ⊗[A] GlobalClosure A W H →ₐ[K] (H → K) :=
  AlgHom.liftEquiv A K _ _ (globalClosureGenericInclusion A W H)

/-- Localization preserves injectivity of the actual global point evaluation. -/
theorem globalClosureGenericMap_injective :
    Function.Injective (globalClosureGenericMap A W H) := by
  apply IsLocalizedModule.injective_of_map_eq A⁰
    (TensorProduct.mk A K (GlobalClosure A W H) 1)
    (g := (globalClosureGenericMap A W H).toLinearMap.restrictScalars A)
  intro x y hxy
  have he : globalClosureGenericInclusion A W H x = globalClosureGenericInclusion A W H y := by
    change (1 : K) • globalClosureGenericInclusion A W H x =
      (1 : K) • globalClosureGenericInclusion A W H y at hxy
    simpa only [one_smul] using hxy
  exact congrArg (fun z => 1 ⊗ₜ[A] z) (globalClosureGenericInclusion_injective A W H he)

/-- The generic fiber dimension is bounded by the actual subgroup cardinality. -/
theorem globalClosure_generic_finrank_le_card :
    Module.finrank K (K ⊗[A] GlobalClosure A W H) ≤ Nat.card H := by
  classical
  let _ := Fintype.ofFinite H
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := (globalClosureGenericMap A W H).toLinearMap)
    (globalClosureGenericMap_injective A W H)
  simpa only [Module.finrank_pi, Nat.card_eq_fintype_card] using h

end FLT.Mazur.EllipticSubgroupChart
