/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupLocalConstantRigidity
public import FLT.Mazur.EllipticSubgroupReducedSections
public import FLT.Mazur.EllipticSubgroupSpecialFiber

/-!
# Injective specialization of the actual local subgroup

Small-ramification rigidity supplies integral delta functions on the closure.
They separate the original sections after every nonzero scalar specialization,
in particular on the actual residue-field fiber.
-/

@[expose] public noncomputable section

open NumberField IsLocalRing ThreeAdicPlan HopfAlgebra.CartierDual
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace FLT.Mazur.EllipticSubgroupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] globalClosureGenericHopfEquiv

variable {K : Type} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K)]
  (W : WeierstrassCurve (v.adicCompletionIntegers K))
  (H : AddSubgroup (W.map (algebraMap (v.adicCompletionIntegers K)
    (v.adicCompletion K))).toProjective.Point) [Finite H]
  (hΔ : IsUnit W.Δ) (p : ℕ) [Fact p.Prime]
  [CharP (ResidueField (v.adicCompletionIntegers K)) p]
  (he : RaynaudParameters.order (p : v.adicCompletionIntegers K) < p - 1)
  (hH : ∀ P : H, p • P = 0)

local notation "A" => v.adicCompletionIntegers K
local instance : IsDedekindDomain A := IsPrincipalIdealRing.isDedekindDomain _

include hΔ he hH

/-- Rigidity constructs a global function taking prescribed integral values on every section. -/
theorem globalClosure_evaluation_interpolation_local (f : H → A) :
    ∃ a : GlobalClosure A W H, ∀ P, globalClosureEvaluation A W H P a = f P := by
  obtain ⟨a, ha⟩ := globalClosureIntegralConstantMap_surjective_local v W H hΔ p he hH
    ((groupAlgebraEquiv A (Multiplicative H)).symm f)
  refine ⟨a, fun P => ?_⟩
  rw [← globalClosureIntegralConstantMap_evaluation, ha]
  exact congrFun ((groupAlgebraEquiv A (Multiplicative H)).apply_symm_apply f) P

/-- Original sections remain distinct over every nontrivial test algebra. -/
theorem globalClosureSpecializedEvaluation_injective_local
    (R : Type) [CommRing R] [Nontrivial R] [Algebra A R] :
    Function.Injective (globalClosureSpecializedEvaluation A W H R) := by
  classical
  intro P Q h
  by_contra hpq
  obtain ⟨a, ha⟩ := globalClosure_evaluation_interpolation_local v W H hΔ p he hH
    (fun S => if S = P then 1 else 0)
  have hv := AlgHom.congr_fun h a
  change algebraMap A R (globalClosureEvaluation A W H P a) =
    algebraMap A R (globalClosureEvaluation A W H Q a) at hv
  simp [ha, Ne.symm hpq] at hv

/-- The original subgroup specializes injectively into the actual residue-field fiber. -/
theorem globalClosureSpecialFiberEvaluation_injective_local :
    Function.Injective (globalClosureSpecialFiberEvaluation A W H) := by
  intro P Q h
  apply globalClosureSpecializedEvaluation_injective_local v W H hΔ p he hH (ResidueField A)
  apply AlgHom.ext
  intro a
  have ht := AlgHom.congr_fun h (1 ⊗ₜ[A] a)
  change algebraMap A (ResidueField A) (globalClosureEvaluation A W H P a) =
    algebraMap A (ResidueField A) (globalClosureEvaluation A W H Q a)
  simpa only [globalClosureSpecialFiberEvaluation_one_tmul] using ht

/-- The actual residue-field algebra is etale in this local small-ramification case. -/
theorem globalClosureSpecialFiber_etale_local :
    Algebra.Etale (ResidueField A) (GlobalClosureSpecialFiber A W H) := by
  let := globalClosure_etale_local v W H hΔ p he hH
  infer_instance

end FLT.Mazur.EllipticSubgroupChart
