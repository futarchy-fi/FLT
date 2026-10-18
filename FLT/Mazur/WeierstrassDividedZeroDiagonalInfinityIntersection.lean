/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalAtlas
public import FLT.Mazur.WeierstrassDividedArithmeticLabeledInitialOverlap

/-!
# Full initial and infinity intersections after the diagonal correction

The original standard D(q) remains the full intersection of both initial
opens and of each with infinity. Each leg retains its entire chart correction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteAtlasIso simultaneousTwistedArithmeticIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "O" => Spec (CommRingCat.of
  (PolynomialNodeOverlap (W.map (algebraMap R Q)) (algebraMap R Q (π ^ 1))))
local notation "P" => polynomialNodeOverlapInclusion
  (W.map (algebraMap R Q)) (algebraMap R Q (π ^ 1))
local notation "B" => arithmeticNodeOverlapOpposite π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "I" => arithmeticInitialOverlapToInfinity hπ data m 1 hj
  H.a1_unit H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "E" => arithmeticZeroFiniteAtlasIso hπ data H m m hj u hu
local notation "G" => simultaneousTwistedArithmeticIso hπ data H m 0 hj u hu
local notation "A" => arithmeticZeroFiniteAtlasObject hπ data H m m hj u hu
local notation "ι" => arithmeticZeroFiniteAtlasChart hπ data H m m hj u hu

/-- The whole original standard overlap enters the actual corrected initial open. -/
def arithmeticZeroDiagonalInitialOverlap (b : Bool) : O ⟶ A (.initial b) :=
  (if b then B else P) ≫ (E (.initial b)).hom

/-- The same entire standard overlap enters the full original infinity chart. -/
def arithmeticZeroDiagonalOverlapToInfinity : O ⟶ A .infinity :=
  I ≫ (E .infinity).hom

local notation "l" => arithmeticZeroDiagonalInitialOverlap hπ data H m hj u hu
local notation "i" => arithmeticZeroDiagonalOverlapToInfinity hπ data H m hj u hu

/-- The two corrected initial opens still meet in exactly the full standard D(q). -/
theorem arithmeticZeroDiagonalAtlas_initial_pair_isPullback :
    IsPullback (l false) (l true) (ι (.initial false)) (ι (.initial true)) := by
  exact (arithmeticLabeledAtlas_initial_isPullback hπ data H m 1 hj).of_iso
    (Iso.refl _) (E (.initial false)) (E (.initial true)) G
    (by simp only [arithmeticZeroDiagonalInitialOverlap, Bool.false_eq_true, ↓reduceIte,
      Iso.refl_hom, Category.id_comp])
    (by simp only [arithmeticZeroDiagonalInitialOverlap, ↓reduceIte,
      Iso.refl_hom, Category.id_comp])
    (arithmeticZeroFiniteAtlasIso_chart hπ data H m m hj u hu (.initial false))
    (arithmeticZeroFiniteAtlasIso_chart hπ data H m m hj u hu (.initial true))

/-- Each full initial/infinity intersection retains its original standard overlap. -/
theorem arithmeticZeroDiagonalAtlas_initial_infinity_isPullback (b : Bool) :
    IsPullback i (l b) (ι .infinity) (ι (.initial b)) := by
  cases b
  · exact (arithmeticLabeledAtlas_first_infinity_isPullback hπ data H m 1 hj).of_iso
      (Iso.refl _) (E .infinity) (E (.initial false)) G
      (by simp only [arithmeticZeroDiagonalOverlapToInfinity, Iso.refl_hom, Category.id_comp])
      (by simp only [arithmeticZeroDiagonalInitialOverlap, Bool.false_eq_true, ↓reduceIte,
        Iso.refl_hom, Category.id_comp])
      (arithmeticZeroFiniteAtlasIso_chart hπ data H m m hj u hu .infinity)
      (arithmeticZeroFiniteAtlasIso_chart hπ data H m m hj u hu (.initial false))
  · exact (arithmeticLabeledAtlas_opposite_infinity_isPullback hπ data H m 1 hj).of_iso
      (Iso.refl _) (E .infinity) (E (.initial true)) G
      (by simp only [arithmeticZeroDiagonalOverlapToInfinity, Iso.refl_hom, Category.id_comp])
      (by simp only [arithmeticZeroDiagonalInitialOverlap, ↓reduceIte,
        Iso.refl_hom, Category.id_comp])
      (arithmeticZeroFiniteAtlasIso_chart hπ data H m m hj u hu .infinity)
      (arithmeticZeroFiniteAtlasIso_chart hπ data H m m hj u hu (.initial true))

/-- All three full corrected source charts agree on their entire common intersection. -/
theorem arithmeticZeroDiagonalAtlas_initial_infinity_triangle :
    l false ≫ ι (.initial false) = l true ≫ ι (.initial true) ∧
      i ≫ ι .infinity = l false ≫ ι (.initial false) :=
  ⟨(arithmeticZeroDiagonalAtlas_initial_pair_isPullback hπ data H m hj u hu).w,
    (arithmeticZeroDiagonalAtlas_initial_infinity_isPullback hπ data H m hj u hu false).w⟩

end FLT.Mazur.WeierstrassDividedDepth
