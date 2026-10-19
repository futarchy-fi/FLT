/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneInitialAtlasTransport
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
  arithmeticOneFiniteAtlasIso simultaneousTwistedArithmeticIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "O" => Spec (CommRingCat.of
  (PolynomialNodeOverlap (W.map (algebraMap R Q)) (algebraMap R Q (π ^ 1))))
local notation "P" => polynomialNodeOverlapInclusion
  (W.map (algebraMap R Q)) (algebraMap R Q (π ^ 1))
local notation "B" => arithmeticNodeOverlapOpposite π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "I" => arithmeticInitialOverlapToInfinity hπ data m 2 hj
  H.a1_unit H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "E" => arithmeticOneFiniteAtlasIso hπ data H m m hj u hu
local notation "T" => arithmeticOneDiagonalInitialTotalOpenIso hπ data H m hj u hu
local notation "G" => simultaneousTwistedArithmeticIso hπ data H m 1 hj u hu
local notation "A" => arithmeticOneFiniteAtlasObject hπ data H m m hj u hu
local notation "ι" => arithmeticOneFiniteAtlasChart hπ data H m m hj u hu

/-- The whole original standard overlap enters the actual corrected initial open. -/
def arithmeticOneDiagonalInitialOverlap (b : Bool) : O ⟶ A (.initial b) :=
  (if b then B else P) ≫ (T b).hom

/-- The same entire standard overlap enters the full original infinity chart. -/
def arithmeticOneDiagonalOverlapToInfinity : O ⟶ A .infinity :=
  I ≫ (E .infinity).hom

local notation "l" => arithmeticOneDiagonalInitialOverlap hπ data H m hj u hu
local notation "i" => arithmeticOneDiagonalOverlapToInfinity hπ data H m hj u hu

/-- The two corrected initial opens still meet in exactly the full standard D(q). -/
theorem arithmeticOneDiagonalAtlas_initial_pair_isPullback :
    IsPullback (l false) (l true) (ι (.initial false)) (ι (.initial true)) := by
  exact (arithmeticLabeledAtlas_initial_isPullback hπ data H m 2 hj).of_iso
    (Iso.refl _) (T false) (T true) G
    (by simp only [arithmeticOneDiagonalInitialOverlap, Bool.false_eq_true, ↓reduceIte,
      Iso.refl_hom, Category.id_comp])
    (by simp only [arithmeticOneDiagonalInitialOverlap, ↓reduceIte,
      Iso.refl_hom, Category.id_comp])
    (arithmeticOneDiagonalInitialTotalOpenIso_global hπ data H m hj u hu false).symm
    (arithmeticOneDiagonalInitialTotalOpenIso_global hπ data H m hj u hu true).symm

/-- Each full initial/infinity intersection retains its original standard overlap. -/
theorem arithmeticOneDiagonalAtlas_initial_infinity_isPullback (b : Bool) :
    IsPullback i (l b) (ι .infinity) (ι (.initial b)) := by
  cases b
  · exact (arithmeticLabeledAtlas_first_infinity_isPullback hπ data H m 2 hj).of_iso
      (Iso.refl _) (E .infinity) (T false) G
      (by simp only [arithmeticOneDiagonalOverlapToInfinity, Iso.refl_hom, Category.id_comp])
      (by simp only [arithmeticOneDiagonalInitialOverlap, Bool.false_eq_true, ↓reduceIte,
        Iso.refl_hom, Category.id_comp])
      (arithmeticOneFiniteAtlasIso_chart hπ data H m m hj u hu .infinity)
      (arithmeticOneDiagonalInitialTotalOpenIso_global hπ data H m hj u hu false).symm
  · exact (arithmeticLabeledAtlas_opposite_infinity_isPullback hπ data H m 2 hj).of_iso
      (Iso.refl _) (E .infinity) (T true) G
      (by simp only [arithmeticOneDiagonalOverlapToInfinity, Iso.refl_hom, Category.id_comp])
      (by simp only [arithmeticOneDiagonalInitialOverlap, ↓reduceIte,
        Iso.refl_hom, Category.id_comp])
      (arithmeticOneFiniteAtlasIso_chart hπ data H m m hj u hu .infinity)
      (arithmeticOneDiagonalInitialTotalOpenIso_global hπ data H m hj u hu true).symm

/-- All three full corrected source charts agree on their entire common intersection. -/
theorem arithmeticOneDiagonalAtlas_initial_infinity_triangle :
    l false ≫ ι (.initial false) = l true ≫ ι (.initial true) ∧
      i ≫ ι .infinity = l false ≫ ι (.initial false) :=
  ⟨(arithmeticOneDiagonalAtlas_initial_pair_isPullback hπ data H m hj u hu).w,
    (arithmeticOneDiagonalAtlas_initial_infinity_isPullback hπ data H m hj u hu false).w⟩

instance arithmeticOneDiagonalOverlapToInfinity_isOpenImmersion : IsOpenImmersion i := by
  exact MorphismProperty.of_isPullback
    (arithmeticOneDiagonalAtlas_initial_infinity_isPullback hπ data H m hj u hu false).flip
    (inferInstanceAs (IsOpenImmersion (ι (.initial false))))

instance arithmeticOneDiagonalInitialOverlap_isOpenImmersion (b : Bool) :
    IsOpenImmersion (l b) := by
  exact MorphismProperty.of_isPullback
    (arithmeticOneDiagonalAtlas_initial_infinity_isPullback hπ data H m hj u hu b)
    (inferInstanceAs (IsOpenImmersion (ι .infinity)))

end FLT.Mazur.WeierstrassDividedDepth
