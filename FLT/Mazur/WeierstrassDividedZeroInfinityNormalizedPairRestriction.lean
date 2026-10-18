/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedNodeRestriction

/-!
# The independent node pair and its actual source presentation under quotient

Glue the original node coefficient maps along the full infinity coefficient map.
The complete pair comparison commutes, as does the actual global inclusion.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart arithmeticZeroFiniteAtlasIso
/-- Five component squares identify a chart restriction of a glued comparison. -/
theorem normalizedPair_chartSquare {A A' B B' C C' Z Z' : Scheme}
    {l : A ⟶ B} {l' : A' ⟶ B'} {v : B ⟶ B'} {d : A ⟶ A'}
    {g : B ⟶ Z} {g' : B' ⟶ Z'} {e : A ⟶ C} {e' : A' ⟶ C'}
    {j : C ⟶ Z} {j' : C' ⟶ Z'} {n : C ⟶ C'} {t : Z ⟶ Z'}
    (hv : l ≫ v = d ≫ l') (hg' : l' ≫ g' = e' ≫ j')
    (hg : l ≫ g = e ≫ j) (ht : j ≫ t = n ≫ j') (he : d ≫ e' = e ≫ n) :
    l ≫ v ≫ g' = l ≫ g ≫ t := by
  rw [← Category.assoc, hv, Category.assoc, hg', ← Category.assoc d, he]
  rw [← Category.assoc l, hg, Category.assoc e j t, ht, Category.assoc]

variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => fun k ↦ Quotient R π k
local notation "τ" => fun k ↦ arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π k
local notation "r" => fun k ↦ rightBranchOpen (Q k) (τ k)
local notation "r'" => fun k ↦ Iso.hom (edgeInversion (Q k)) ≫ r k
local notation "i" => fun k ↦ arithmeticZeroDiagonalOverlapToInfinity hπ data H k hj u hu
local notation "l" => fun k ↦ arithmeticZeroDiagonalInitialOverlap hπ data H k hj u hu
local notation "a" => fun k b ↦ pushout.inl (i k) (l k b)
local notation "N" => closingNormalizedRestriction data H m
local notation "ρ" => closingOverlapRestriction (R := R) (π := π) m
local notation "S" => arithmeticZeroDiagonalAtlasRestriction hπ data H hj u hu m
local notation "e" => fun k ↦ arithmeticZeroInfinityNormalizedNodeIso hπ data H k hj u hu
local notation "G" => fun k ↦ arithmeticZeroInfinityNormalizedPairIso hπ data H k hj u hu
local notation "k" => fun v ↦ arithmeticZeroInfinityNormalizedPairToGlobal hπ data H v hj u hu
local notation "j" => fun v ↦ arithmeticZeroInfinityNormalizedToGlobal hπ data H v hj u hu
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H m 0 hj u hu
local notation "D" => arithmeticZeroInfinityNormalizedNodeRestriction hπ data H m hj u hu

/-- The independent pair follows the original uncorrected whole-node coefficient arrows. -/
def arithmeticZeroInfinityNormalizedTargetRestriction :
    arithmeticZeroInfinityNormalizedTargetPair data H m ⟶
      arithmeticZeroInfinityNormalizedTargetPair data H (m + 1) :=
  pushout.map (r m) (r' m) (r (m + 1)) (r' (m + 1)) N N ρ
    (arithmeticZeroInfinityNormalizedRight_restriction data H m)
    (by rw [Category.assoc, arithmeticZeroInfinityNormalizedRight_restriction,
          arithmeticZeroInfinityNormalizedInversion_restriction_assoc])

local notation "t" => arithmeticZeroInfinityNormalizedTargetRestriction data H m

omit [IsDomain R] [IsBezout R] in
/-- The first target node has the full original coefficient square. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedTargetRestriction_first :
    pushout.inl (r m) (r' m) ≫ t = N ≫ pushout.inl (r (m + 1)) (r' (m + 1)) :=
  pushout.inl_desc _ _ _

omit [IsDomain R] [IsBezout R] in
/-- The opposite target node has the full original coefficient square. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedTargetRestriction_opposite :
    pushout.inr (r m) (r' m) ≫ t = N ≫ pushout.inr (r (m + 1)) (r' (m + 1)) :=
  pushout.inr_desc _ _ _

/-- The actual pair presentation glues its two whole-node source quotient arrows. -/
def arithmeticZeroInfinityNormalizedPairRestriction :
    arithmeticZeroInfinityNormalizedSourcePair hπ data H m hj u hu ⟶
      arithmeticZeroInfinityNormalizedSourcePair hπ data H (m + 1) hj u hu :=
  pushout.map (a m false) (a m true) (a (m + 1) false) (a (m + 1) true)
    (D false) (D true) (S .infinity)
    (arithmeticZeroInfinityNormalizedNodeRestriction_infinity hπ data H m hj u hu false)
    (arithmeticZeroInfinityNormalizedNodeRestriction_infinity hπ data H m hj u hu true)

local notation "v" => arithmeticZeroInfinityNormalizedPairRestriction hπ data H m hj u hu

/-- The first complete source node retains its constructed quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedPairRestriction_first :
    pushout.inl (a m false) (a m true) ≫ v =
      D false ≫ pushout.inl (a (m + 1) false) (a (m + 1) true) := pushout.inl_desc _ _ _

/-- The opposite complete source node retains its constructed quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedPairRestriction_opposite :
    pushout.inr (a m false) (a m true) ≫ v =
      D true ≫ pushout.inr (a (m + 1) false) (a (m + 1) true) := pushout.inr_desc _ _ _

/-- The first whole source node commutes with the independent target quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedPairIso_restriction_first :
    pushout.inl (a m false) (a m true) ≫ v ≫ (G (m + 1)).hom =
      pushout.inl (a m false) (a m true) ≫ (G m).hom ≫ t :=
  normalizedPair_chartSquare
    (arithmeticZeroInfinityNormalizedPairRestriction_first hπ data H m hj u hu)
    (arithmeticZeroInfinityNormalizedPairIso_first hπ data H (m + 1) hj u hu)
    (arithmeticZeroInfinityNormalizedPairIso_first hπ data H m hj u hu)
    (arithmeticZeroInfinityNormalizedTargetRestriction_first data H m)
    (arithmeticZeroInfinityNormalizedNodeRestriction_node hπ data H m hj u hu false)

/-- The opposite whole source node commutes with the independent target quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedPairIso_restriction_opposite :
    pushout.inr (a m false) (a m true) ≫ v ≫ (G (m + 1)).hom =
      pushout.inr (a m false) (a m true) ≫ (G m).hom ≫ t :=
  normalizedPair_chartSquare
    (arithmeticZeroInfinityNormalizedPairRestriction_opposite hπ data H m hj u hu)
    (arithmeticZeroInfinityNormalizedPairIso_opposite hπ data H (m + 1) hj u hu)
    (arithmeticZeroInfinityNormalizedPairIso_opposite hπ data H m hj u hu)
    (arithmeticZeroInfinityNormalizedTargetRestriction_opposite data H m)
    (arithmeticZeroInfinityNormalizedNodeRestriction_node hπ data H m hj u hu true)

/-- The two entire source nodes commute with the independent pair quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedPairIso_restriction :
    v ≫ (G (m + 1)).hom = (G m).hom ≫ t := by
  apply pushout.hom_ext
  · exact arithmeticZeroInfinityNormalizedPairIso_restriction_first hπ data H m hj u hu
  · exact arithmeticZeroInfinityNormalizedPairIso_restriction_opposite hπ data H m hj u hu

/-- The complete pair quotient is the original global quotient on its entire image. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedPairRestriction_global :
    v ≫ k (m + 1) = k m ≫ q := by
  apply pushout.hom_ext
  · rw [arithmeticZeroInfinityNormalizedPairRestriction_first_assoc,
      arithmeticZeroInfinityNormalizedPairToGlobal_first,
      arithmeticZeroInfinityNormalizedPairToGlobal_first_assoc,
      arithmeticZeroInfinityNormalizedNodeRestriction_global]
  · rw [arithmeticZeroInfinityNormalizedPairRestriction_opposite_assoc,
      arithmeticZeroInfinityNormalizedPairToGlobal_opposite,
      arithmeticZeroInfinityNormalizedPairToGlobal_opposite_assoc,
      arithmeticZeroInfinityNormalizedNodeRestriction_global]

end FLT.Mazur.WeierstrassDividedDepth
