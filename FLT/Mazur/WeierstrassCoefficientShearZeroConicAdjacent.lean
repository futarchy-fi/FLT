/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearScaleOneGluedPunctures
public import FLT.Mazur.WeierstrassSuccessiveZeroConicShearPunctures
public import FLT.Mazur.WeierstrassDilatationResidueFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections

/-!
# Actual split residue conic punctures equal the next retained lines

Both signed adjacent formulas now use the independently constructed
original conic immersion. No equation or coefficient transport is discarded.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (m : ℕ) (hm : j + 2 + m ≤ n)
  (D : SplitNodeDepth W π depth) (hk0 : start + j = 0)
  (hk : 2 * (start + j + 1) ≤ depth)
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
local notation "F" => zeroResidueConicImmersion D (start + j) hk0 hk
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

/-- The entire original first conic puncture is the reciprocal next first line. -/
theorem coefficientShearZeroConicFirst_adjacent :
    P₁ ≫ F ≫ B = ρ₁ ≫ p ≫ line 0 (middle_first_root U) := by
  rw [← Category.assoc,
    zeroResidueConicFirst_spec_eq_shear D hk0 hk d hs hp g3 g4 hr gc, Category.assoc]
  exact coefficientShearScaleOneFirst_gluedPuncture hπ data K 0 j hj hjNext m hm
    hs hp h3 h4 hr a ha

/-- The original opposite puncture retains both its signed scale and the next slope. -/
theorem coefficientShearZeroConicSecond_adjacent :
    P₂ ≫ F ≫ B = ρ₂ ≫ p ≫ line (-(U).a₁) (middle_second_root U) := by
  rw [← Category.assoc,
    zeroResidueConicSecond_spec_eq_shear D hk0 hk d hs hp g3 g4 hr gc, Category.assoc]
  exact coefficientShearScaleOneSecond_gluedPuncture hπ data K 0 j hj hjNext m hm
    hs hp h3 h4 hr a ha

end FLT.Mazur.WeierstrassDividedDepth
