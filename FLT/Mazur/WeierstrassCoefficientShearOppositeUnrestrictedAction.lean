/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearReciprocalUnrestrictedAction
public import FLT.Mazur.WeierstrassCoefficientShearLineActionReflection
import all FLT.Mazur.WeierstrassCoefficientShearLineActionReflection
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections

/-!
# The unrestricted line actions after the actual opposite-root comparison

Both original line embeddings exchange with unchanged affine coordinates.
The acting input is explicitly composed with Laurent inversion on the full torus.
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
local notation "hl₁" => coefficientShearRetainedLine_structure hπ data K 0
  (j + 2 + m) hm (Fin.mk (j + 1) (by omega)) (coefficientShearAdjacent_scale K hp)
  hp h3 h4 hr 0 (middle_first_root U)
local notation "hl₂" => coefficientShearRetainedLine_structure hπ data K 0
  (j + 2 + m) hm (Fin.mk (j + 1) (by omega)) (coefficientShearAdjacent_scale K hp)
  hp h3 h4 hr (-(U).a₁) (middle_second_root U)
variable {B₀ : Type} [CommRing B₀] [Algebra (ResidueField R) B₀] (t₀ z₀ : B₀ˣ)
local notation "pt" => fun q => (laurentUnitOverPoint (R := K) q).left
local notation "cond₁" => show pt t₀ ≫ t = ((pt z₀ ≫ p) ≫ L₁) ≫ g from by
  simpa only [Category.assoc] using LaurentLineActionEvaluation.condition g L₁ hl₁ t₀ z₀
local notation "cond₂" => show pt t₀ ≫ t = ((pt z₀ ≫ p) ≫ L₂) ≫ g from by
  simpa only [Category.assoc] using LaurentLineActionEvaluation.condition g L₂ hl₂ t₀ z₀

/-- The opposite-root second line pairs with the full inverted torus input. -/
theorem coefficientShearOppositeSecond_unitsCondition :
    (pt t₀ ≫ ι) ≫ t = ((pt z₀ ≫ p) ≫ Ls (-(Us).a₁) (middle_second_root Us)) ≫ gs :=
  coefficientShearLineReflection_firstCondition hπ data K 0
    (j + 2 + m) (j + 1) hm (by omega) a (h).1 (h).2.1
    (h).2.2.1 (h).2.2.2.1 (h).2.2.2.2 (coefficientShearAdjacent_scale K hp) hp h3 h4
    (pt t₀) (pt z₀ ≫ p) cond₁

include hj hk0 in
/-- The full opposite-root second-line action retains the explicit inverse character. -/
theorem coefficientShearOppositeSecond_unitsAction :
    pullback.lift (pt t₀ ≫ ι) ((pt z₀ ≫ p) ≫ Ls (-(Us).a₁) (middle_second_root Us))
        (coefficientShearOppositeSecond_unitsCondition hπ data j hjNext m hm D hk
          t₀ z₀) ≫ As = (pt (t₀⁻¹ * z₀) ≫ p) ≫ Ls (-(Us).a₁) (middle_second_root Us) := by
  have H := coefficientShearLineReflection_firstAction hπ data K 0
    (j + 2 + m) (j + 1) hm (by omega) a (h).1 (h).2.1
    (h).2.2.1 (h).2.2.2.1 (h).2.2.2.2 (coefficientShearAdjacent_scale K hp) hp h3 h4
    (pt t₀) (pt z₀ ≫ p) cond₁
  refine H.trans ?_
  have ho := congrArg (· ≫ (C).hom)
    (coefficientShearFirstLine_unitsAction hπ data j hj hjNext m hm D hk0 hk t₀ z₀)
  have hl := coefficientShearLineReflection_first hπ data K 0 (j + 2 + m) (j + 1)
    hm (by omega) (h).2.1 (coefficientShearAdjacent_scale K hp) hp h3 h4
    (pt (t₀⁻¹ * z₀) ≫ p)
  refine Eq.trans ?_ hl
  simp only [LaurentLineActionEvaluation.action, Category.assoc] at ho ⊢
  exact ho

/-- The opposite-root first line pairs with the same full inverted torus input. -/
theorem coefficientShearOppositeFirst_unitsCondition :
    (pt t₀ ≫ ι) ≫ t = ((pt z₀ ≫ p) ≫ Ls 0 (middle_first_root Us)) ≫ gs :=
  coefficientShearLineReflection_secondCondition hπ data K 0
    (j + 2 + m) (j + 1) hm (by omega) a (h).1 (h).2.1
    (h).2.2.1 (h).2.2.2.1 (h).2.2.2.2 (coefficientShearAdjacent_scale K hp) hp h3 h4
    (pt t₀) (pt z₀ ≫ p) cond₂

include hj hk0 in
/-- The full opposite-root first-line action retains the explicit positive character. -/
theorem coefficientShearOppositeFirst_unitsAction :
    pullback.lift (pt t₀ ≫ ι) ((pt z₀ ≫ p) ≫ Ls 0 (middle_first_root Us))
        (coefficientShearOppositeFirst_unitsCondition hπ data j hjNext m hm D hk
          t₀ z₀) ≫ As = (pt (t₀ * z₀) ≫ p) ≫ Ls 0 (middle_first_root Us) := by
  have H := coefficientShearLineReflection_secondAction hπ data K 0
    (j + 2 + m) (j + 1) hm (by omega) a (h).1 (h).2.1
    (h).2.2.1 (h).2.2.2.1 (h).2.2.2.2 (coefficientShearAdjacent_scale K hp) hp h3 h4
    (pt t₀) (pt z₀ ≫ p) cond₂
  refine H.trans ?_
  have ho := congrArg (· ≫ (C).hom)
    (coefficientShearSecondLine_unitsAction hπ data j hj hjNext m hm D hk0 hk t₀ z₀)
  have hl := coefficientShearLineReflection_second hπ data K 0 (j + 2 + m) (j + 1)
    hm (by omega) (h).2.1 (coefficientShearAdjacent_scale K hp) hp h3 h4
    (pt (t₀ * z₀) ≫ p)
  refine Eq.trans ?_ hl
  simp only [LaurentLineActionEvaluation.action, Category.assoc] at ho ⊢
  exact ho

end FLT.Mazur.WeierstrassDividedDepth
