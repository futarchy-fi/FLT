/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearReciprocalUnrestrictedAction
public import FLT.Mazur.WeierstrassCoefficientShearLineSpecialization
import all FLT.Mazur.WeierstrassCoefficientShearLineSpecialization
public import FLT.Mazur.WeierstrassRootShearCoefficientConditions
public import FLT.Mazur.LaurentUnitCoefficientPoint
public import FLT.Mazur.WeierstrassCoefficientShearSpecializationExt
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections

/-!
# Explicit signed Laurent formulas in the actual specialized model

Both independent units are arbitrary, including the identity.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (m : ℕ) (hm : j + 2 + m ≤ n)
  (D : SplitNodeDepth W π depth) (hk0 : start + j = 0)
  (hk : 2 * (start + j + 1) < depth)
local notation "K" => ResidueField R
local notation "h3" => (dividedLinear_adjacent_residue_zero D data hjNext hk).1
local notation "h4" => (dividedLinear_adjacent_residue_zero D data hjNext hk).2
local notation "V" => W.map (residue R)
local notation "U" => rootShearCurve V 0
local notation "a" => WeierstrassDilatation.residueTangentUnit D
local notation "hp" => Iff.mpr (residue_eq_zero_iff π)
  (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
local notation "hr" => show (0 : K) ^ 2 + algebraMap R K W.a₁ * 0 -
    algebraMap R K W.a₂ = 0 from by
  rw [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, zero_sub, neg_eq_zero]
  exact (residue_eq_zero_iff _).mpr D.a₂_mem
local notation "line" => coefficientShearRetainedLine hπ data K 0 (j + 2 + m) hm
  (Fin.mk (j + 1) (by omega)) (coefficientShearAdjacent_scale K hp) hp h3 h4 hr

local notation "g" => coefficientShearGluedStructure hπ data K 0 (j + 2 + m) hm
local notation "t" => Over.hom (MultiplicativeGroupScheme.gm K)
local notation "h" => splitDepth_zeroRoot_conditions D
local notation "A" => coefficientShearTorusAction hπ data K 0 (j + 2 + m) hm a
  (h).1 (h).2.1 (h).2.2.1 (h).2.2.2.1 (h).2.2.2.2
local notation "L₁" => line 0 (middle_first_root U)
local notation "L₂" => line (-(U).a₁) (middle_second_root U)

local notation "hl₁" => coefficientShearRetainedLine_structure hπ data K 0
  (j + 2 + m) hm (Fin.mk (j + 1) (by omega)) (coefficientShearAdjacent_scale K hp)
  hp h3 h4 hr 0 (middle_first_root U)
local notation "hl₂" => coefficientShearRetainedLine_structure hπ data K 0
  (j + 2 + m) hm (Fin.mk (j + 1) (by omega)) (coefficientShearAdjacent_scale K hp)
  hp h3 h4 hr (-(U).a₁) (middle_second_root U)
variable (T : Type) [CommRing T] [Algebra R T] [Algebra (ResidueField R) T]
  [IsScalarTower R (ResidueField R) T]
local notation "f" => IsScalarTower.toAlgHom R K T
local notation "rT" => (f) 0
local notation "b" => Units.map (f).toRingHom a
local notation "hb" => rootShearCoefficient_tangent W f 0 a (h).1
local notation "hv" => rootShearCoefficient_root W f 0 (h).2.1
local notation "van" => rootShearCoefficient_vanishing W f
  (h).2.2.1 (h).2.2.2.1 (h).2.2.2.2
local notation "UT" => rootShearCurve (W.map (algebraMap R T)) rT
local notation "hpT" => show algebraMap R T π = 0 from by
  rw [IsScalarTower.algebraMap_apply R K T, ResidueField.algebraMap_eq, hp, map_zero]
local notation "h3T" => show algebraMap R T (data ⟨j + 2, by omega⟩).b3 = 0 from by
  rw [IsScalarTower.algebraMap_apply R K T, ResidueField.algebraMap_eq, h3, map_zero]
local notation "h4T" => show algebraMap R T (data ⟨j + 2, by omega⟩).b4 = 0 from by
  rw [IsScalarTower.algebraMap_apply R K T, ResidueField.algebraMap_eq, h4, map_zero]
local notation "lineT" => coefficientShearRetainedLine hπ data T rT (j + 2 + m) hm
  (Fin.mk (j + 1) (by omega)) (coefficientShearAdjacent_scale T hpT) hpT h3T h4T hv
local notation "LT₁" => lineT 0 (middle_first_root UT)
local notation "LT₂" => lineT (-(UT).a₁) (middle_second_root UT)
local notation "gT" => coefficientShearGluedStructure hπ data T rT (j + 2 + m) hm
local notation "AT" => coefficientShearTorusAction hπ data T rT (j + 2 + m) hm b
  hb hv (van).1 (van).2.1 (van).2.2
local notation "M" => coefficientShearSpecialization hπ data K T 0 rT (j + 2 + m) hm f
local notation "hlT₁" => coefficientShearRetainedLine_structure hπ data T rT
  (j + 2 + m) hm (Fin.mk (j + 1) (by omega)) (coefficientShearAdjacent_scale T hpT)
  hpT h3T h4T hv 0 (middle_first_root UT)
local notation "hlT₂" => coefficientShearRetainedLine_structure hπ data T rT
  (j + 2 + m) hm (Fin.mk (j + 1) (by omega)) (coefficientShearAdjacent_scale T hpT)
  hpT h3T h4T hv (-(UT).a₁) (middle_second_root UT)
local notation "pT" => Spec.map (CommRingCat.ofHom
  (Polynomial.toLaurent : Polynomial T →+* T[T;T⁻¹]))
local notation "pK" => Spec.map (CommRingCat.ofHom
  (Polynomial.toLaurent : Polynomial K →+* K[T;T⁻¹]))
local notation "ptT" => fun q => (laurentUnitOverPoint (R := T) q).left
local notation "ptK" => fun q => (laurentUnitOverPoint (R := K) q).left
local notation "act" => LaurentLineActionEvaluation.action
variable {B₀ : Type} [CommRing B₀] [Algebra T B₀] [Algebra (ResidueField R) B₀]
  [IsScalarTower (ResidueField R) T B₀] (q z : B₀ˣ)

include hj hk0 hk in
/-- The first line's unrestricted inverse character holds in the actual coefficient model. -/
theorem coefficientShearFirstLine_specializedUnitsAction :
    act gT LT₁ hlT₁ q z AT = ptT (q⁻¹ * z) ≫ pT ≫ LT₁ := by
  apply coefficientShearSpecialization_hom_ext hπ data K T 0 rT (j + 2 + m) hm f
  · rw [LaurentLineActionEvaluation.action_structure _ _ _ _ _ _
      (coefficientShearTorusAction_structure hπ data T rT (j + 2 + m) hm b
        hb hv (van).1 (van).2.1 (van).2.2),
      LaurentLineActionEvaluation.point_structure _ _ hlT₁]
  · have H := coefficientShearLineSpecialization_firstAction hπ data K T f 0
      (j + 1) hjNext m hm a b rfl (h).1 (h).2.1 (h).2.2.1 (h).2.2.2.1 (h).2.2.2.2
      hb hv (van).1 (van).2.1 (van).2.2
      (coefficientShearAdjacent_scale K hp) hp h3 h4
      (coefficientShearAdjacent_scale T hpT) hpT h3T h4T (ptT q) (ptT z ≫ pT)
      (by simpa only [Category.assoc] using
        LaurentLineActionEvaluation.condition gT LT₁ hlT₁ q z)
    simp only [show (f).toRingHom = algebraMap K T from rfl,
      Category.assoc, laurentPolynomialPuncture_coefficient] at H
    simp only [← Category.assoc, laurentUnitOverPoint_coefficient] at H
    have Hline := coefficientShearLineSpecialization_first hπ data K T f 0
      (j + 1) hjNext m hm (h).2.1 hv
      (coefficientShearAdjacent_scale K hp) hp h3 h4
      (coefficientShearAdjacent_scale T hpT) hpT h3T h4T (ptT (q⁻¹ * z) ≫ pT)
    simp only [show (f).toRingHom = algebraMap K T from rfl,
      Category.assoc, laurentPolynomialPuncture_coefficient] at Hline
    simp only [← Category.assoc, laurentUnitOverPoint_coefficient] at Hline
    have HF := coefficientShearFirstLine_unitsAction hπ data j hj hjNext m hm D hk0 hk q z
    change act gT LT₁ hlT₁ q z AT ≫ M = _
    simp only [LaurentLineActionEvaluation.action, Category.assoc] at H Hline HF ⊢
    exact H.trans (HF.trans Hline.symm)

include hj hk0 hk in
/-- The second line's unrestricted positive character holds in the actual coefficient model. -/
theorem coefficientShearSecondLine_specializedUnitsAction :
    act gT LT₂ hlT₂ q z AT = ptT (q * z) ≫ pT ≫ LT₂ := by
  apply coefficientShearSpecialization_hom_ext hπ data K T 0 rT (j + 2 + m) hm f
  · rw [LaurentLineActionEvaluation.action_structure _ _ _ _ _ _
      (coefficientShearTorusAction_structure hπ data T rT (j + 2 + m) hm b
        hb hv (van).1 (van).2.1 (van).2.2),
      LaurentLineActionEvaluation.point_structure _ _ hlT₂]
  · have H := coefficientShearLineSpecialization_secondAction hπ data K T f 0
      (j + 1) hjNext m hm a b rfl (h).1 (h).2.1 (h).2.2.1 (h).2.2.2.1 (h).2.2.2.2
      hb hv (van).1 (van).2.1 (van).2.2
      (coefficientShearAdjacent_scale K hp) hp h3 h4
      (coefficientShearAdjacent_scale T hpT) hpT h3T h4T (ptT q) (ptT z ≫ pT)
      (by simpa only [Category.assoc] using
        LaurentLineActionEvaluation.condition gT LT₂ hlT₂ q z)
    simp only [show (f).toRingHom = algebraMap K T from rfl,
      Category.assoc, laurentPolynomialPuncture_coefficient] at H
    simp only [← Category.assoc, laurentUnitOverPoint_coefficient] at H
    have Hline := coefficientShearLineSpecialization_second hπ data K T f 0
      (j + 1) hjNext m hm (h).2.1 hv
      (coefficientShearAdjacent_scale K hp) hp h3 h4
      (coefficientShearAdjacent_scale T hpT) hpT h3T h4T (ptT (q * z) ≫ pT)
    simp only [show (f).toRingHom = algebraMap K T from rfl,
      Category.assoc, laurentPolynomialPuncture_coefficient] at Hline
    simp only [← Category.assoc, laurentUnitOverPoint_coefficient] at Hline
    have HF := coefficientShearSecondLine_unitsAction hπ data j hj hjNext m hm D hk0 hk q z
    change act gT LT₂ hlT₂ q z AT ≫ M = _
    simp only [LaurentLineActionEvaluation.action, Category.assoc] at H Hline HF ⊢
    exact H.trans (HF.trans Hline.symm)

end FLT.Mazur.WeierstrassDividedDepth
