/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticExtensionChartClosure
public import FLT.Mazur.EllipticSubgroupHenselianSpecialization

/-!
# The good-reduction closure of the transported prime-order point

The original field extension and variable change give the actual prime-order
subgroup. Its constructed closure is finite flat; small ramification makes
it etale and its original smooth reduction injective. The bound six suffices
for primes at least seventeen, as in the semistable extension construction.
-/

@[expose] public noncomputable section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing EllipticSubgroupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] globalClosureGenericHopfEquiv

variable {R K L : Type} [CommRing R] [Field K] [Field L] [CharZero L]
  [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
  [DecidableEq K] [DecidableEq L]
  (A : ValuationSubring L) [IsDiscreteValuationRing A] [HenselianLocalRing A]
  (W : WeierstrassCurve R) (U : WeierstrassCurve A)
  [(W.map (algebraMap R L)).IsElliptic] (C : VariableChange L)
  (hC : C • W.map (algebraMap R L) = U.map (algebraMap A L))
  (P : (W.map (algebraMap R K)).toAffine.Point)
  (p : ℕ) [Fact p.Prime] (hP : p • P = 0) (hP0 : P ≠ 0) (hΔ : IsUnit U.Δ)

local notation "H" => ellipticExtensionProjectiveSubgroup A W U C hC P
local instance : IsDedekindDomain A := IsPrincipalIdealRing.isDedekindDomain _

include hP hP0 in
omit [CharZero L] [IsDiscreteValuationRing A] [HenselianLocalRing A] in
/-- The transported prime-order subgroup is finite, from the original nonzero torsion point. -/
theorem ellipticExtensionProjectiveSubgroup_finite : Finite H :=
  Nat.finite_of_card_ne_zero
    ((ellipticExtensionProjectiveSubgroup_card A W U C hC P hP hP0).trans_ne
      (Fact.out : p.Prime).ne_zero)

/-- The original transported point has its actual finite-flat good-reduction closure. -/
def ellipticExtensionGoodReductionModel : ThreeAdicPlan.FF A L := by
  letI := ellipticExtensionProjectiveSubgroup_finite A W U C hC P p hP hP0
  exact globalClosureFiniteFlatModel A U H hΔ

omit [HenselianLocalRing A] in
/-- The constructed model has exactly the order of the original torsion generator. -/
theorem ellipticExtensionGoodReductionModel_card :
    Nat.card (ellipticExtensionGoodReductionModel A W U C hC P p hP hP0 hΔ).Points = p := by
  let _ := ellipticExtensionProjectiveSubgroup_finite A W U C hC P p hP hP0
  exact (globalClosureFiniteFlatModel_card A U H hΔ).trans
    (ellipticExtensionProjectiveSubgroup_card A W U C hC P hP hP0)

variable [CharP (ResidueField A) p]

include hP hP0 hΔ in
/-- The actual transported subgroup closure is etale under the S2a absolute order bound. -/
theorem ellipticExtensionGoodReductionClosure_etale (hp17 : 17 ≤ p)
    (he6 : RaynaudParameters.order (p : A) ≤ 6) :
    Algebra.Etale A (GlobalClosure A U H) := by
  let _ := ellipticExtensionProjectiveSubgroup_finite A W U C hC P p hP hP0
  exact globalClosure_etale_henselian A U H hΔ p (by omega)
    (ellipticExtensionProjectiveSubgroup_card A W U C hC P hP hP0)

include hP hP0 in
/-- The original transported subgroup specializes injectively under the same S2a bound. -/
theorem ellipticExtensionGoodReduction_specialization_injective (hp17 : 17 ≤ p)
    (he6 : RaynaudParameters.order (p : A) ≤ 6) :
    Function.Injective (subgroupSmoothReduction A U H
      (subgroup_le_ellipticE0_of_unit_discriminant A U H hΔ)) := by
  let _ := ellipticExtensionProjectiveSubgroup_finite A W U C hC P p hP hP0
  exact subgroupSmoothReduction_injective_henselian A U H hΔ p (by omega)
    (ellipticExtensionProjectiveSubgroup_card A W U C hC P hP hP0)

end FLT.Mazur
