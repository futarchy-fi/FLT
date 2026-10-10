/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ConstantPrimeScalarFiltration
public import FLT.Mazur.EllipticSubgroupConstantModelComparison

/-!
# Constant prime-order closure over a Henselian DVR

The actual constant-to-closure morphism is an integral isomorphism when the
absolute ramification order is less than p minus one. This uses no identification
of the fraction field with a number-field completion.
-/

@[expose] public noncomputable section

open ThreeAdicPlan IsLocalRing HopfAlgebra.CartierDual

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

include hΔ he hc in
/-- The original integral evaluation map is surjective by the constructed scalar filtration. -/
theorem globalClosureIntegralConstantMap_surjective_henselian :
    Function.Surjective (globalClosureIntegralConstantMap A W H) := by
  exact ModelHom.surjective_of_henselian_scalarFiltration p he
    (constantGroupModel_prime_scalarFiltration A K H p hc)
    (globalClosureConstantModelHom A W H hΔ)
    (globalClosureConstantModelHom_generic_bijective A W H hΔ)

/-- The actual original constant comparison is the integral Hopf isomorphism. -/
def globalClosureHenselianConstantIso :
    (constantGroupModel A K H).Iso (globalClosureFiniteFlatModel A W H hΔ) :=
  BialgEquiv.ofBijective (globalClosureConstantModelHom A W H hΔ)
    ⟨globalClosureIntegralConstantMap_injective A W H,
      globalClosureIntegralConstantMap_surjective_henselian A W H hΔ p he hc⟩

/-- The isomorphism uses precisely the constructed section-evaluation map. -/
theorem globalClosureHenselianConstantIso_hom :
    (globalClosureHenselianConstantIso A W H hΔ p he hc).toBialgHom =
      globalClosureConstantModelHom A W H hΔ := rfl

include hΔ he hc in
/-- Every prescribed integral function on the original prime-order subgroup interpolates. -/
theorem globalClosure_evaluation_interpolation_henselian (f : H → A) :
    ∃ a : GlobalClosure A W H, ∀ P, globalClosureEvaluation A W H P a = f P := by
  obtain ⟨a, ha⟩ := globalClosureIntegralConstantMap_surjective_henselian A W H hΔ p he hc
    ((groupAlgebraEquiv A (Multiplicative H)).symm f)
  refine ⟨a, fun P => ?_⟩
  rw [← globalClosureIntegralConstantMap_evaluation, ha]
  exact congrFun ((groupAlgebraEquiv A (Multiplicative H)).apply_symm_apply f) P

include hΔ he hc in
/-- The original closure is integrally etale under the absolute ramification bound. -/
theorem globalClosure_etale_henselian : Algebra.Etale A (GlobalClosure A W H) := by
  let : Algebra.Etale A (constantGroupModel A K H).CoordinateRing :=
    Algebra.Etale.of_equiv (constantGroupCoordinates A K H).symm
  exact Algebra.Etale.of_equiv (globalClosureHenselianConstantIso A W H hΔ p he hc).symm.toAlgEquiv

end FLT.Mazur.EllipticSubgroupChart
