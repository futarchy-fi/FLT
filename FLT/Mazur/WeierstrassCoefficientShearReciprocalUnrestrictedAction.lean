/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearReciprocalUniversalAction
public import FLT.Mazur.WeierstrassDividedLinearResidueBounds
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections

/-!
# Unrestricted actual reciprocal action over arbitrary test algebras

Specialize the whole universal-pair comparison. No invertibility of the tangent
parameter minus one is required, and arbitrary nonreduced test algebras are allowed.
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
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "e" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
local notation "h3" => (dividedLinear_adjacent_residue_zero D data hjNext hk).1
local notation "h4" => (dividedLinear_adjacent_residue_zero D data hjNext hk).2
local notation "V" => W.map (residue R)
local notation "U" => rootShearCurve V 0
local notation "a" => WeierstrassDilatation.residueTangentUnit D
local notation "c" => residue R (Data.b6 d)
local notation "hp" => Iff.mpr (residue_eq_zero_iff π)
  (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
local notation "hs" => show algebraMap R K (π ^ (start + j)) = 1 from by
  simp only [hk0, pow_zero, map_one]
local notation "hr" => show (0 : K) ^ 2 + algebraMap R K W.a₁ * 0 -
    algebraMap R K W.a₂ = 0 from by
  rw [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, zero_sub, neg_eq_zero]
  exact (residue_eq_zero_iff _).mpr D.a₂_mem
local notation "g3" => And.left (coefficientShearAdjacent_coefficients hπ d e K hp)
local notation "g4" => And.left (And.right (coefficientShearAdjacent_coefficients hπ d e K hp))
local notation "gc" => And.right (And.right (coefficientShearAdjacent_coefficients hπ d e K hp))
local notation "ha" => Eq.trans (WeierstrassDilatation.residueTangentUnit_val D)
  (Eq.symm (rootShearZero_tangent V))
local notation "F" => zeroResidueConicImmersion D (start + j) hk0 (Nat.le_of_lt hk)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
local notation "B" => coefficientShearRetainedTensorChart hπ data K 0
  (j + 2 + m) hm (Fin.mk j (by omega))
local notation "P₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (conicPuncturedFirst V c gc)))
local notation "P₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (conicPuncturedSecond V c gc)))
local notation "p" => Spec.map (CommRingCat.ofHom
  (Polynomial.toLaurent : Polynomial K →+* K[T;T⁻¹]))
local notation "ρ₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (PolygonScaledReciprocal.reciprocal (a⁻¹))))
local notation "ρ₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (PolygonScaledReciprocal.reciprocal ((-a)⁻¹))))
local notation "line" => coefficientShearRetainedLine hπ data K 0 (j + 2 + m) hm
  (Fin.mk (j + 1) (by omega)) (coefficientShearAdjacent_scale K hp) hp h3 h4 hr

local notation "J" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (smoothHorizontalResidueConic D)))
local notation "τ" => smoothHorizontalTangentUnit D
local notation "z" => smoothHorizontalConicUnit D
local notation "u" => laurentUnitOverPoint (R := K) τ
local notation "g" => coefficientShearGluedStructure hπ data K 0 (j + 2 + m) hm
local notation "t" => Over.hom (MultiplicativeGroupScheme.gm K)
local notation "h" => splitDepth_zeroRoot_conditions D
local notation "A" => coefficientShearTorusAction hπ data K 0 (j + 2 + m) hm a
  (h).1 (h).2.1 (h).2.2.1 (h).2.2.2.1 (h).2.2.2.2
local notation "L₁" => line 0 (middle_first_root U)
local notation "L₂" => line (-(U).a₁) (middle_second_root U)

local notation "q₁" => smoothHorizontalReciprocalUnit D (a⁻¹)
local notation "q₂" => smoothHorizontalReciprocalUnit D ((-a)⁻¹)
local notation "ev" => fun q => Spec.map
  (CommRingCat.ofHom (smoothHorizontalLaurentEvaluation D q).toRingHom)

open ProjectiveLineUniversalAction
local notation "hl₁" => coefficientShearRetainedLine_structure hπ data K 0
  (j + 2 + m) hm (Fin.mk (j + 1) (by omega)) (coefficientShearAdjacent_scale K hp)
  hp h3 h4 hr 0 (middle_first_root U)
local notation "hl₂" => coefficientShearRetainedLine_structure hπ data K 0
  (j + 2 + m) hm (Fin.mk (j + 1) (by omega)) (coefficientShearAdjacent_scale K hp)
  hp h3 h4 hr (-(U).a₁) (middle_second_root U)
local notation "act" => LaurentLineActionEvaluation.action
variable {B₀ : Type} [CommRing B₀] [Algebra (ResidueField R) B₀] (t₀ z₀ : B₀ˣ)
local notation "Q₁" => Units.map (algebraMap K B₀) (a⁻¹) * z₀⁻¹
local notation "Q₂" => Units.map (algebraMap K B₀) ((-a)⁻¹) * z₀⁻¹
local notation "pt" => fun q => (laurentUnitOverPoint (R := K) q).left
local notation "φ" => laurentPairEvaluation («K» := K) t₀⁻¹ z₀
local notation "φs" => Spec.map (CommRingCat.ofHom (φ).toRingHom)

include hj hk0 hk
/-- The first reciprocal coordinate has the inverse character at every torus parameter. -/
theorem coefficientShearReciprocalFirst_unrestricted :
    act g L₁ hl₁ t₀ Q₁ A = pt (t₀⁻¹ * Q₁) ≫ p ≫ L₁ := by
  have H := congrArg (φs ≫ ·)
    (coefficientShearReciprocalFirst_universal hπ data j hj hjNext m hm D hk0 hk h3 h4)
  rw [LaurentLineActionEvaluation.action_natural,
    ← Category.assoc φs, laurentUnitOverPoint_natural] at H
  simpa only [map_mul, map_inv, laurentPairEvaluation_tangentUnit,
    laurentPairEvaluation_reciprocalUnit, inv_inv] using H

/-- The signed opposite reciprocal coordinate has the positive character everywhere. -/
theorem coefficientShearReciprocalSecond_unrestricted :
    act g L₂ hl₂ t₀ Q₂ A = pt (t₀ * Q₂) ≫ p ≫ L₂ := by
  have H := congrArg (φs ≫ ·)
    (coefficientShearReciprocalSecond_universal hπ data j hj hjNext m hm D hk0 hk h3 h4)
  rw [LaurentLineActionEvaluation.action_natural,
    ← Category.assoc φs, laurentUnitOverPoint_natural] at H
  simpa only [map_mul, map_inv, laurentPairEvaluation_tangentUnit,
    laurentPairEvaluation_reciprocalUnit, inv_inv] using H

/-- Every punctured first-line coordinate has the unrestricted inverse tangent character. -/
theorem coefficientShearFirstLine_unitsAction :
    act g L₁ hl₁ t₀ z₀ A = pt (t₀⁻¹ * z₀) ≫ p ≫ L₁ := by
  have H := coefficientShearReciprocalFirst_unrestricted hπ data j hj hjNext m hm D hk0 hk
    t₀ (z₀⁻¹ * Units.map (algebraMap K B₀) (a⁻¹))
  simpa only [mul_inv_rev, inv_inv, mul_inv_cancel_left] using H

/-- Every punctured opposite-line coordinate has the unrestricted positive tangent character. -/
theorem coefficientShearSecondLine_unitsAction :
    act g L₂ hl₂ t₀ z₀ A = pt (t₀ * z₀) ≫ p ≫ L₂ := by
  have H := coefficientShearReciprocalSecond_unrestricted hπ data j hj hjNext m hm D hk0 hk
    t₀ (z₀⁻¹ * Units.map (algebraMap K B₀) ((-a)⁻¹))
  simpa only [mul_inv_rev, inv_inv, mul_inv_cancel_left] using H

end FLT.Mazur.WeierstrassDividedDepth
