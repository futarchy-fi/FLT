/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupHenselianConstantRigidity
public import FLT.Mazur.EllipticSubgroupReductionComparison
public import FLT.Mazur.EllipticSubgroupSpecialFiber

/-!
# Prime-order specialization under the absolute ramification bound

Integral interpolation separates the actual reduced sections. The previously
proved geometric comparison transfers this to the original smooth-reduction
homomorphism. The special fiber itself is etale of rank p.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

namespace FLT.Mazur.EllipticSubgroupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] globalClosureGenericHopfEquiv

variable {K : Type} [Field K] [CharZero K] (A : ValuationSubring K)
  [IsDiscreteValuationRing A] [HenselianLocalRing A] (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) [Finite H]
  (hΔ : IsUnit W.Δ) (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
  (he : RaynaudParameters.order (p : A) < p - 1) (hc : Nat.card H = p)

local instance : IsDedekindDomain A := IsPrincipalIdealRing.isDedekindDomain _

include hΔ he hc

/-- Every nonzero test algebra separates the original subgroup sections. -/
theorem globalClosureSpecializedEvaluation_injective_henselian
    (R : Type) [CommRing R] [Nontrivial R] [Algebra A R] :
    Function.Injective (globalClosureSpecializedEvaluation A W H R) := by
  classical
  intro P Q h
  by_contra hpq
  obtain ⟨a, ha⟩ := globalClosure_evaluation_interpolation_henselian A W H hΔ p he hc
    (fun S => if S = P then 1 else 0)
  have hv := AlgHom.congr_fun h a
  change algebraMap A R (globalClosureEvaluation A W H P a) =
    algebraMap A R (globalClosureEvaluation A W H Q a) at hv
  simp [ha, Ne.symm hpq] at hv

/-- The actual special-fiber evaluations are injective on the original prime-order subgroup. -/
theorem globalClosureSpecialFiberEvaluation_injective_henselian :
    Function.Injective (globalClosureSpecialFiberEvaluation A W H) := by
  intro P Q h
  apply globalClosureSpecializedEvaluation_injective_henselian A W H hΔ p he hc (ResidueField A)
  apply AlgHom.ext
  intro a
  have ht := AlgHom.congr_fun h (1 ⊗ₜ[A] a)
  change algebraMap A (ResidueField A) (globalClosureEvaluation A W H P a) =
    algebraMap A (ResidueField A) (globalClosureEvaluation A W H Q a)
  simpa only [globalClosureSpecialFiberEvaluation_one_tmul] using ht

/-- The original smooth reduction is injective on the good-reduction prime-order subgroup. -/
theorem subgroupSmoothReduction_injective_henselian :
    Function.Injective (subgroupSmoothReduction A W H
      (subgroup_le_ellipticE0_of_unit_discriminant A W H hΔ)) := by
  intro P Q h
  exact globalClosureSpecializedEvaluation_injective_henselian A W H hΔ p he hc
    (ResidueField A) ((subgroupSmoothReduction_eq_iff A W H _ P Q).mp h)

/-- The actual residue algebra is etale, including when p is the residue characteristic. -/
theorem globalClosureSpecialFiber_etale_henselian :
    Algebra.Etale (ResidueField A) (GlobalClosureSpecialFiber A W H) := by
  let := globalClosure_etale_henselian A W H hΔ p he hc
  infer_instance

omit hΔ he [CharZero K] [HenselianLocalRing A] [Fact p.Prime]
  [CharP (ResidueField A) p] in
/-- The actual special fiber has rank equal to the original prime order. -/
theorem globalClosureSpecialFiber_finrank_prime :
    Module.finrank (ResidueField A) (GlobalClosureSpecialFiber A W H) = p :=
  (globalClosureSpecialFiber_finrank A W H).trans hc

end FLT.Mazur.EllipticSubgroupChart
