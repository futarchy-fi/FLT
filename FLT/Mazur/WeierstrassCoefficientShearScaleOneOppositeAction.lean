/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearScaleOneAdjacentAction
public import FLT.Mazur.WeierstrassCoefficientShearLineActionReflection
public import FLT.Mazur.WeierstrassDividedLinearResidueBounds
import all FLT.Mazur.WeierstrassCoefficientShearLineActionReflection
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections

/-!
# Explicit adjacent-line action formulas at the opposite chosen tangent root

Transport the proved original root-zero formulas through the actual root
comparison and independently identified full lines. The acting parameter is inverted.
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

local notation "s" => (-(V).a₁ - 0)
local notation "Us" => rootShearCurve V s
local notation "hb" => rootShearOpposite_tangent V 0 a (h).1
local notation "hsr" => rootShearOpposite_root V 0 (h).2.1
local notation "C" => coefficientShearRootChange hπ data K 0 s (j + 2 + m) hm
local notation "ι" => Spec.map (CommRingCat.ofHom
  (LaurentPolynomial.invert (R := K)).toRingHom)
local notation "Ls" => coefficientShearRetainedLine hπ data K s (j + 2 + m) hm
  (Fin.mk (j + 1) (by omega)) (coefficientShearAdjacent_scale K hp) hp h3 h4 hsr
local notation "As" => coefficientShearTorusAction hπ data K s (j + 2 + m) hm (-a)
  hb hsr (h).2.2.1 (h).2.2.2.1 (h).2.2.2.2
local notation "gs" => coefficientShearGluedStructure hπ data K s (j + 2 + m) hm
local notation "Q₁" => J ≫ ρ₁ ≫ p
local notation "Q₂" => J ≫ ρ₂ ≫ p

include hj hk0 hk
/-- The actual opposite-root second line is in the inverted-parameter action domain. -/
theorem coefficientShearScaleOneOppositeSecond_condition :
    ((u).left ≫ ι) ≫ t = (Q₁ ≫ Ls (-(Us).a₁) (middle_second_root Us)) ≫ gs := by
  have hz : (u).left ≫ t = (Q₁ ≫ L₁) ≫ g := by
    simpa only [Category.assoc] using
      coefficientShearScaleOneAdjacentFirst_condition hπ data j hj hjNext m hm D hk0 hk h3 h4
  exact coefficientShearLineReflection_firstCondition hπ data K 0
    (j + 2 + m) (j + 1) hm (by omega) a (h).1 (h).2.1
    (h).2.2.1 (h).2.2.2.1 (h).2.2.2.2 (coefficientShearAdjacent_scale K hp) hp h3 h4
    (u).left Q₁ hz

/-- The explicit first-root action becomes the actual opposite-root second-line action. -/
theorem coefficientShearTorusAction_scaleOneOppositeSecond :
    pullback.lift ((u).left ≫ ι) (Q₁ ≫ Ls (-(Us).a₁) (middle_second_root Us))
        (coefficientShearScaleOneOppositeSecond_condition hπ data j hj hjNext m hm
          D hk0 hk) ≫ As =
      Spec.map (CommRingCat.ofHom (smoothHorizontalLaurentEvaluation D (τ * z)).toRingHom) ≫
        ρ₁ ≫ p ≫ Ls (-(Us).a₁) (middle_second_root Us) := by
  have hz : (u).left ≫ t = (Q₁ ≫ L₁) ≫ g := by
    simpa only [Category.assoc] using
      coefficientShearScaleOneAdjacentFirst_condition hπ data j hj hjNext m hm D hk0 hk h3 h4
  have H := coefficientShearLineReflection_firstAction hπ data K 0
    (j + 2 + m) (j + 1) hm (by omega) a (h).1 (h).2.1
    (h).2.2.1 (h).2.2.2.1 (h).2.2.2.2 (coefficientShearAdjacent_scale K hp) hp h3 h4
    (u).left Q₁ hz
  refine H.trans ?_
  have ho := congrArg (fun f => f ≫ (C).hom)
    (coefficientShearTorusAction_scaleOneAdjacentFirst hπ data j hj hjNext m hm D hk0 hk h3 h4)
  have hl := coefficientShearLineReflection_first hπ data K 0 (j + 2 + m) (j + 1)
    hm (by omega) (h).2.1 (coefficientShearAdjacent_scale K hp) hp h3 h4
    (Spec.map (CommRingCat.ofHom (smoothHorizontalLaurentEvaluation D (τ * z)).toRingHom) ≫
      ρ₁ ≫ p)
  refine Eq.trans ?_ hl
  simp only [Category.assoc] at ho ⊢
  exact ho

include hj hk0 hk
/-- The actual opposite-root first line is in the inverted-parameter action domain. -/
theorem coefficientShearScaleOneOppositeFirst_condition :
    ((u).left ≫ ι) ≫ t = (Q₂ ≫ Ls 0 (middle_first_root Us)) ≫ gs := by
  have hz : (u).left ≫ t = (Q₂ ≫ L₂) ≫ g := by
    simpa only [Category.assoc] using
      coefficientShearScaleOneAdjacentSecond_condition hπ data j hj hjNext m hm D hk0 hk h3 h4
  exact coefficientShearLineReflection_secondCondition hπ data K 0
    (j + 2 + m) (j + 1) hm (by omega) a (h).1 (h).2.1
    (h).2.2.1 (h).2.2.2.1 (h).2.2.2.2 (coefficientShearAdjacent_scale K hp) hp h3 h4
    (u).left Q₂ hz

/-- The explicit second-root action becomes the actual opposite-root first-line action. -/
theorem coefficientShearTorusAction_scaleOneOppositeFirst :
    pullback.lift ((u).left ≫ ι) (Q₂ ≫ Ls 0 (middle_first_root Us))
        (coefficientShearScaleOneOppositeFirst_condition hπ data j hj hjNext m hm
          D hk0 hk) ≫ As =
      Spec.map (CommRingCat.ofHom (smoothHorizontalLaurentEvaluation D (τ⁻¹ * z)).toRingHom) ≫
        ρ₂ ≫ p ≫ Ls 0 (middle_first_root Us) := by
  have hz : (u).left ≫ t = (Q₂ ≫ L₂) ≫ g := by
    simpa only [Category.assoc] using
      coefficientShearScaleOneAdjacentSecond_condition hπ data j hj hjNext m hm D hk0 hk h3 h4
  have H := coefficientShearLineReflection_secondAction hπ data K 0
    (j + 2 + m) (j + 1) hm (by omega) a (h).1 (h).2.1
    (h).2.2.1 (h).2.2.2.1 (h).2.2.2.2 (coefficientShearAdjacent_scale K hp) hp h3 h4
    (u).left Q₂ hz
  refine H.trans ?_
  have ho := congrArg (fun f => f ≫ (C).hom)
    (coefficientShearTorusAction_scaleOneAdjacentSecond hπ data j hj hjNext m hm D hk0 hk h3 h4)
  have hl := coefficientShearLineReflection_second hπ data K 0 (j + 2 + m) (j + 1)
    hm (by omega) (h).2.1 (coefficientShearAdjacent_scale K hp) hp h3 h4
    (Spec.map (CommRingCat.ofHom (smoothHorizontalLaurentEvaluation D (τ⁻¹ * z)).toRingHom) ≫
      ρ₂ ≫ p)
  refine Eq.trans ?_ hl
  simp only [Category.assoc] at ho ⊢
  exact ho

end FLT.Mazur.WeierstrassDividedDepth
