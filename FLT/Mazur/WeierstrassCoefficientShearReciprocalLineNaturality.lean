/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearReciprocalLineAction
public import FLT.Mazur.LaurentUnitPointNaturality
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections

/-!
# Actual reciprocal actions after a change of test algebra

Both full scheme-map formulas specialize along arbitrary algebra maps out
of the original smooth product. Nonreduced target algebras are allowed.
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

variable {B₀ : Type} [CommRing B₀] [Algebra (ResidueField R) B₀]
  (φ : SmoothHorizontalResidueRing D →ₐ[ResidueField R] B₀)
local notation "φs" => Spec.map (CommRingCat.ofHom φ.toRingHom)
local notation "φu" => Units.map φ.toMonoidHom
local notation "pt" => fun q => (laurentUnitOverPoint (R := K) q).left

omit [IsDomain R] [IsBezout R] in
/-- Every complete Laurent evaluation specializes to its mapped unit. -/
theorem coefficientShearReciprocalEvaluation_natural (q : (SmoothHorizontalResidueRing D)ˣ) :
    φs ≫ ev q = pt (φu q) := laurentUnitOverPoint_natural φ q

include hj hk0 hk
/-- The mapped first input and mapped tangent unit retain the original coefficient map. -/
theorem coefficientShearReciprocalFirst_naturalCondition :
    pt (φu τ) ≫ t = (pt (φu q₁) ≫ p ≫ L₁) ≫ g := by
  calc
    _ = (φs ≫ (u).left) ≫ t :=
      congrArg (· ≫ t) (laurentUnitOverPoint_natural φ τ).symm
    _ = φs ≫ ((ev q₁ ≫ p ≫ L₁) ≫ g) := by
      rw [Category.assoc, coefficientShearReciprocalFirst_condition
        hπ data j hj hjNext m hm D hk0 hk h3 h4]
    _ = _ := by
      rw [← Category.assoc φs, ← Category.assoc φs,
        coefficientShearReciprocalEvaluation_natural]

/-- The opposite mapped input retains its signed reciprocal parameter. -/
theorem coefficientShearReciprocalSecond_naturalCondition :
    pt (φu τ) ≫ t = (pt (φu q₂) ≫ p ≫ L₂) ≫ g := by
  calc
    _ = (φs ≫ (u).left) ≫ t :=
      congrArg (· ≫ t) (laurentUnitOverPoint_natural φ τ).symm
    _ = φs ≫ ((ev q₂ ≫ p ≫ L₂) ≫ g) := by
      rw [Category.assoc, coefficientShearReciprocalSecond_condition
        hπ data j hj hjNext m hm D hk0 hk h3 h4]
    _ = _ := by
      rw [← Category.assoc φs, ← Category.assoc φs,
        coefficientShearReciprocalEvaluation_natural]

/-- The first actual action keeps the inverse character over every test algebra. -/
theorem coefficientShearTorusAction_reciprocalFirst_natural :
    pullback.lift (pt (φu τ)) (pt (φu q₁) ≫ p ≫ L₁)
        (coefficientShearReciprocalFirst_naturalCondition hπ data j hj hjNext m hm
          D hk0 hk h3 h4 φ) ≫ A = pt ((φu τ)⁻¹ * φu q₁) ≫ p ≫ L₁ := by
  have hl : pullback.lift (pt (φu τ)) (pt (φu q₁) ≫ p ≫ L₁)
      (coefficientShearReciprocalFirst_naturalCondition hπ data j hj hjNext m hm
        D hk0 hk h3 h4 φ) =
      φs ≫ pullback.lift (u).left (ev q₁ ≫ p ≫ L₁)
        (coefficientShearReciprocalFirst_condition hπ data j hj hjNext m hm
          D hk0 hk h3 h4) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      exact (laurentUnitOverPoint_natural φ τ).symm
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc φs,
        coefficientShearReciprocalEvaluation_natural]
  rw [hl, Category.assoc, coefficientShearTorusAction_reciprocalFirst
    hπ data j hj hjNext m hm D hk0 hk h3 h4]
  rw [← Category.assoc φs, coefficientShearReciprocalEvaluation_natural, map_mul, map_inv]

/-- The opposite actual action keeps the positive character over every test algebra. -/
theorem coefficientShearTorusAction_reciprocalSecond_natural :
    pullback.lift (pt (φu τ)) (pt (φu q₂) ≫ p ≫ L₂)
        (coefficientShearReciprocalSecond_naturalCondition hπ data j hj hjNext m hm
          D hk0 hk h3 h4 φ) ≫ A = pt (φu τ * φu q₂) ≫ p ≫ L₂ := by
  have hl : pullback.lift (pt (φu τ)) (pt (φu q₂) ≫ p ≫ L₂)
      (coefficientShearReciprocalSecond_naturalCondition hπ data j hj hjNext m hm
        D hk0 hk h3 h4 φ) =
      φs ≫ pullback.lift (u).left (ev q₂ ≫ p ≫ L₂)
        (coefficientShearReciprocalSecond_condition hπ data j hj hjNext m hm
          D hk0 hk h3 h4) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      exact (laurentUnitOverPoint_natural φ τ).symm
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc φs,
        coefficientShearReciprocalEvaluation_natural]
  rw [hl, Category.assoc, coefficientShearTorusAction_reciprocalSecond
    hπ data j hj hjNext m hm D hk0 hk h3 h4]
  rw [← Category.assoc φs, coefficientShearReciprocalEvaluation_natural, map_mul]

end FLT.Mazur.WeierstrassDividedDepth
