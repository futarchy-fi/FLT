/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearScaleOneAdjacentAction
public import FLT.Mazur.WeierstrassCoefficientShearReciprocalLineAction
public import FLT.Mazur.WeierstrassCoefficientShearSeparated
public import FLT.Mazur.WeierstrassSmoothHorizontalPairDensity
public import FLT.Mazur.LaurentPairReciprocalUnits
public import FLT.Mazur.LaurentLineActionDensity
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections

/-!
# The unrestricted reciprocal action on the universal Laurent pair

Density of the independently computed horizontal source determines morphisms on
both whole Laurent variables. The original glued target is proper and separated.
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
variable (h3 : residue R (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩).b3 = 0)
  (h4 : residue R (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩).b4 = 0)
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
local notation "u₀" => laurentPairTangentUnit K
local notation "z₀" => laurentPairSecondUnit K
local notation "Q₁" => laurentPairReciprocalUnit K (a⁻¹)
local notation "Q₂" => laurentPairReciprocalUnit K ((-a)⁻¹)
local notation "pt" => fun q => (laurentUnitOverPoint (R := K) q).left
local notation "hl₁" => coefficientShearRetainedLine_structure hπ data K 0
  (j + 2 + m) hm (Fin.mk (j + 1) (by omega)) (coefficientShearAdjacent_scale K hp)
  hp h3 h4 hr 0 (middle_first_root U)
local notation "hl₂" => coefficientShearRetainedLine_structure hπ data K 0
  (j + 2 + m) hm (Fin.mk (j + 1) (by omega)) (coefficientShearAdjacent_scale K hp)
  hp h3 h4 hr (-(U).a₁) (middle_second_root U)
local notation "φ" => laurentPairEvaluation («K» := K) τ⁻¹ z
local notation "φs" => Spec.map (CommRingCat.ofHom (φ).toRingHom)
local notation "act" => LaurentLineActionEvaluation.action

include hj hk0 hk
/-- The inverse tangent character on the full independent universal pair. -/
theorem coefficientShearReciprocalFirst_universal :
    act g L₁ hl₁ u₀ Q₁ A = pt (u₀⁻¹ * Q₁) ≫ p ≫ L₁ := by
  apply LaurentLineActionEvaluation.action_eq_of_dominant
    («K» := K) («B» := K[T;T⁻¹][T;T⁻¹]) (C := SmoothHorizontalResidueRing D) g L₁ hl₁ A
    (coefficientShearTorusAction_structure hπ data K 0 (j + 2 + m) hm a
      (h).1 (h).2.1 (h).2.2.1 (h).2.2.2.1 (h).2.2.2.2) φ u₀ Q₁ (u₀⁻¹ * Q₁)
  simp only [map_mul, map_inv, laurentPairEvaluation_tangentUnit,
    laurentPairEvaluation_reciprocalUnit, inv_inv]
  exact coefficientShearTorusAction_reciprocalFirst hπ data j hj hjNext m hm
    D hk0 hk h3 h4

/-- The positive tangent character on the full opposite-line universal pair. -/
theorem coefficientShearReciprocalSecond_universal :
    act g L₂ hl₂ u₀ Q₂ A = pt (u₀ * Q₂) ≫ p ≫ L₂ := by
  apply LaurentLineActionEvaluation.action_eq_of_dominant
    («K» := K) («B» := K[T;T⁻¹][T;T⁻¹]) (C := SmoothHorizontalResidueRing D) g L₂ hl₂ A
    (coefficientShearTorusAction_structure hπ data K 0 (j + 2 + m) hm a
      (h).1 (h).2.1 (h).2.2.1 (h).2.2.2.1 (h).2.2.2.2) φ u₀ Q₂ (u₀ * Q₂)
  simp only [map_mul, map_inv, laurentPairEvaluation_tangentUnit,
    laurentPairEvaluation_reciprocalUnit, inv_inv]
  exact coefficientShearTorusAction_reciprocalSecond hπ data j hj hjNext m hm
    D hk0 hk h3 h4

end FLT.Mazur.WeierstrassDividedDepth
