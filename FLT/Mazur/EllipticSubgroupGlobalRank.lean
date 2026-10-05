/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupGenericSectionInjective
public import FLT.Mazur.EllipticSubgroupGlobalRankBound

/-!
# The global generic coordinate algebra and its exact rank

Affineness turns distinct generic sections into separating global functions.
Finite-point interpolation identifies the actual generic coordinate algebra
with the split algebra of subgroup points, giving the integral rank over a DVR.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.EllipticSubgroupChart

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) [Finite H]

/-- Global evaluation distinguishes the actual integral subgroup sections. -/
theorem globalClosureEvaluation_injective :
    Function.Injective (globalClosureEvaluation A W H) := by
  intro P Q h
  apply genericSection_injective A W H
  apply congrArg (fun s => Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ s)
  apply ext_of_isAffine
  apply (cancel_mono (Scheme.ΓSpecIso (.of A)).hom).mp
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom h

/-- Integral global coordinates already separate points after embedding in the field. -/
theorem globalClosureGenericInclusion_separates (P Q : H) (hPQ : P ≠ Q) :
    ∃ a, globalClosureGenericInclusion A W H a P ≠
      globalClosureGenericInclusion A W H a Q := by
  by_contra! h
  apply hPQ
  apply globalClosureEvaluation_injective A W H
  apply AlgHom.ext
  intro a
  exact Subtype.coe_injective (h a)

omit [Finite H] in
/-- The generic global evaluation of a scalar-extended integral function. -/
@[simp] theorem globalClosureGenericMap_one_tmul (a : GlobalClosure A W H) :
    globalClosureGenericMap A W H (1 ⊗ₜ[A] a) =
      globalClosureGenericInclusion A W H a := by
  change (1 : K) • globalClosureGenericInclusion A W H a = _
  exact one_smul K _

/-- Interpolation makes generic global evaluation onto the full subgroup point algebra. -/
theorem globalClosureGenericMap_surjective :
    Function.Surjective (globalClosureGenericMap A W H) := by
  apply finitePointAlgebra_surjective
  intro P Q hPQ
  obtain ⟨a, ha⟩ := globalClosureGenericInclusion_separates A W H P Q hPQ
  exact ⟨1 ⊗ₜ[A] a, by simpa only [globalClosureGenericMap_one_tmul] using ha⟩

/-- The actual generic coordinate algebra is the split algebra of subgroup points. -/
def globalClosureGenericEquiv : K ⊗[A] GlobalClosure A W H ≃ₐ[K] (H → K) :=
  AlgEquiv.ofBijective (globalClosureGenericMap A W H)
    ⟨globalClosureGenericMap_injective A W H, globalClosureGenericMap_surjective A W H⟩

/-- The generic rank is exactly the number of actual subgroup points. -/
theorem globalClosure_generic_finrank :
    Module.finrank K (K ⊗[A] GlobalClosure A W H) = Nat.card H := by
  classical
  let _ := Fintype.ofFinite H
  rw [(globalClosureGenericEquiv A W H).toLinearEquiv.finrank_eq]
  simp only [Module.finrank_pi, Nat.card_eq_fintype_card]

/-- Over a DVR the finite flat closure has rank equal to the subgroup cardinality. -/
theorem globalClosure_finrank [IsDedekindDomain A] :
    Module.finrank A (GlobalClosure A W H) = Nat.card H := by
  rw [globalClosure_finrank_generic A W H, globalClosure_generic_finrank A W H]

end FLT.Mazur.EllipticSubgroupChart
