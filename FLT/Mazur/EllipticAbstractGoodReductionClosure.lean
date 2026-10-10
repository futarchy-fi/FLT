/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticValuationRingEquation
public import FLT.Mazur.ValuationRingHenselianModel
public import FLT.Mazur.EllipticExtensionGoodReductionClosure

/-!
# Good-reduction closure over the abstract extension DVR

Realize the supplied DVR and equation in the fraction field, preserving the
original extension and variable change. The closure of the original prime-order
point is finite flat of rank p, and small ramification makes its actual smooth
reduction injective and its coordinate algebra etale.
-/

@[expose] public noncomputable section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing EllipticSubgroupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] globalClosureGenericHopfEquiv

variable {R S K L : Type} [CommRing R] [CommRing S] [IsDomain S]
  [IsDiscreteValuationRing S] [Field K] [Field L]
  [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
  [Algebra S L] [IsFractionRing S L] [DecidableEq K] [DecidableEq L]
  (W : WeierstrassCurve R) (U : WeierstrassCurve S)
  [(W.map (algebraMap R L)).IsElliptic] (C : VariableChange L)
  (hC : C • W.map (algebraMap R L) = U.map (algebraMap S L))
  (P : (W.map (algebraMap R K)).toAffine.Point)

local notation "A" => fractionValuationSubring S L
local notation "V" => fractionValuationEquation (L := L) U
local notation "hV" => fractionValuationEquation_variableChange _ U C hC

local instance : IsDiscreteValuationRing A := fractionValuationSubring_isDiscreteValuationRing S L
local instance : IsDedekindDomain A := IsPrincipalIdealRing.isDedekindDomain _

/-- The actual transported cyclic subgroup, with the original variable change. -/
def abstractExtensionProjectiveSubgroup :
    AddSubgroup ((V).map (algebraMap A L)).toProjective.Point :=
  ellipticExtensionProjectiveSubgroup A W V C hV P

local notation "H" => abstractExtensionProjectiveSubgroup W U C hC P

variable (p : ℕ) [Fact p.Prime] (hP : p • P = 0) (hP0 : P ≠ 0)

include hP hP0 in
/-- The realized subgroup retains the exact original prime order. -/
theorem abstractExtensionProjectiveSubgroup_card : Nat.card H = p :=
  ellipticExtensionProjectiveSubgroup_card A W V C hV P hP hP0

include hP hP0 in
/-- Finiteness follows from the original point, rather than an assumed closure. -/
theorem abstractExtensionProjectiveSubgroup_finite : Finite H :=
  Nat.finite_of_card_ne_zero
    ((abstractExtensionProjectiveSubgroup_card W U C hC P p hP hP0).trans_ne
      (Fact.out : p.Prime).ne_zero)

variable [CharZero L] [(U.map (algebraMap S L)).HasGoodReduction S]

local notation "hΔ" => fractionValuationEquation_discriminant_unit (L := L) U

/-- The constructed finite-flat closure uses the realized original equation. -/
def abstractExtensionGoodReductionModel : ThreeAdicPlan.FF A L := by
  letI := abstractExtensionProjectiveSubgroup_finite W U C hC P p hP hP0
  exact globalClosureFiniteFlatModel A V H hΔ

/-- The constructed closure has the original prime rank. -/
theorem abstractExtensionGoodReductionModel_card :
    Nat.card (abstractExtensionGoodReductionModel W U C hC P p hP hP0).Points = p := by
  let _ := abstractExtensionProjectiveSubgroup_finite W U C hC P p hP hP0
  exact (globalClosureFiniteFlatModel_card A V H hΔ).trans
    (abstractExtensionProjectiveSubgroup_card W U C hC P p hP hP0)

variable [HenselianLocalRing S] [CharP (ResidueField S) p]
  (he : RaynaudParameters.order (p : S) < p - 1)

local instance : HenselianLocalRing A := fractionValuationSubring_henselian S L
local instance : CharP (ResidueField A) p := fractionValuationSubring_residue_char S L p

include hP hP0 he in
/-- Small ramification makes the actual closure of the original point etale. -/
theorem abstractExtensionGoodReductionClosure_etale : Algebra.Etale A (GlobalClosure A V H) := by
  let _ := abstractExtensionProjectiveSubgroup_finite W U C hC P p hP hP0
  apply globalClosure_etale_henselian A V H hΔ p
  · rwa [fractionValuationSubring_prime_order]
  · exact abstractExtensionProjectiveSubgroup_card W U C hC P p hP hP0

include hP hP0 he in
/-- The original prime subgroup specializes injectively in the realized good equation. -/
theorem abstractExtensionGoodReduction_specialization_injective :
    Function.Injective (subgroupSmoothReduction A V H
      (subgroup_le_ellipticE0_of_unit_discriminant A V H hΔ)) := by
  let _ := abstractExtensionProjectiveSubgroup_finite W U C hC P p hP hP0
  apply subgroupSmoothReduction_injective_henselian A V H hΔ p
  · rwa [fractionValuationSubring_prime_order]
  · exact abstractExtensionProjectiveSubgroup_card W U C hC P p hP hP0

end FLT.Mazur
