/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneInfinityNormalizedNodeRestriction
public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedPairRestriction

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
  arithmeticOneFiniteInitialIso arithmeticInitialFactorRatioChart arithmeticOneFiniteAtlasIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => fun k ↦ Quotient R π k
local notation "τ" => fun k ↦ arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π k
local notation "r" => fun k ↦ rightBranchOpen (Q k) (τ k)
local notation "r'" => fun k ↦ Iso.hom (edgeInversion (Q k)) ≫ r k
local notation "i" => fun k ↦ arithmeticOneDiagonalOverlapToInfinity hπ data H k hj u hu
local notation "l" => fun k ↦ arithmeticOneDiagonalInitialOverlap hπ data H k hj u hu
local notation "a" => fun k b ↦ pushout.inl (i k) (l k b)
local notation "N" => closingNormalizedRestriction data H m
local notation "ρ" => closingOverlapRestriction (R := R) (π := π) m
local notation "S" => arithmeticOneDiagonalAtlasRestriction hπ data H hj u hu m
local notation "e" => fun k ↦ arithmeticOneInfinityNormalizedNodeIso hπ data H k hj u hu
local notation "G" => fun k ↦ arithmeticOneInfinityNormalizedPairIso hπ data H k hj u hu
local notation "k" => fun v ↦ arithmeticOneInfinityNormalizedPairToGlobal hπ data H v hj u hu
local notation "j" => fun v ↦ arithmeticOneInfinityNormalizedToGlobal hπ data H v hj u hu
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H m 1 hj u hu
local notation "D" => arithmeticOneInfinityNormalizedNodeRestriction hπ data H m hj u hu

/-- The independent pair follows the original uncorrected whole-node coefficient arrows. -/
def arithmeticOneInfinityNormalizedTargetRestriction :
    arithmeticOneInfinityNormalizedTargetPair data H m ⟶
      arithmeticOneInfinityNormalizedTargetPair data H (m + 1) :=
  pushout.map (r m) (r' m) (r (m + 1)) (r' (m + 1)) N N ρ
    (arithmeticOneInfinityNormalizedRight_restriction data H m)
    (by rw [Category.assoc, arithmeticOneInfinityNormalizedRight_restriction,
          arithmeticOneInfinityNormalizedInversion_restriction_assoc])

local notation "t" => arithmeticOneInfinityNormalizedTargetRestriction data H m

omit [IsDomain R] [IsBezout R] in
/-- The first target node has the full original coefficient square. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedTargetRestriction_first :
    pushout.inl (r m) (r' m) ≫ t = N ≫ pushout.inl (r (m + 1)) (r' (m + 1)) :=
  pushout.inl_desc _ _ _

omit [IsDomain R] [IsBezout R] in
/-- The opposite target node has the full original coefficient square. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedTargetRestriction_opposite :
    pushout.inr (r m) (r' m) ≫ t = N ≫ pushout.inr (r (m + 1)) (r' (m + 1)) :=
  pushout.inr_desc _ _ _

/-- The actual pair presentation glues its two whole-node source quotient arrows. -/
def arithmeticOneInfinityNormalizedPairRestriction :
    arithmeticOneInfinityNormalizedSourcePair hπ data H m hj u hu ⟶
      arithmeticOneInfinityNormalizedSourcePair hπ data H (m + 1) hj u hu :=
  pushout.map (a m false) (a m true) (a (m + 1) false) (a (m + 1) true)
    (D false) (D true) (S .infinity)
    (arithmeticOneInfinityNormalizedNodeRestriction_infinity hπ data H m hj u hu false)
    (arithmeticOneInfinityNormalizedNodeRestriction_infinity hπ data H m hj u hu true)

local notation "v" => arithmeticOneInfinityNormalizedPairRestriction hπ data H m hj u hu

/-- The first complete source node retains its constructed quotient. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedPairRestriction_first :
    pushout.inl (a m false) (a m true) ≫ v =
      D false ≫ pushout.inl (a (m + 1) false) (a (m + 1) true) := pushout.inl_desc _ _ _

/-- The opposite complete source node retains its constructed quotient. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedPairRestriction_opposite :
    pushout.inr (a m false) (a m true) ≫ v =
      D true ≫ pushout.inr (a (m + 1) false) (a (m + 1) true) := pushout.inr_desc _ _ _

/-- The first whole source node commutes with the independent target quotient. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedPairIso_restriction_first :
    pushout.inl (a m false) (a m true) ≫ v ≫ (G (m + 1)).hom =
      pushout.inl (a m false) (a m true) ≫ (G m).hom ≫ t :=
  normalizedPair_chartSquare
    (arithmeticOneInfinityNormalizedPairRestriction_first hπ data H m hj u hu)
    (arithmeticOneInfinityNormalizedPairIso_first hπ data H (m + 1) hj u hu)
    (arithmeticOneInfinityNormalizedPairIso_first hπ data H m hj u hu)
    (arithmeticOneInfinityNormalizedTargetRestriction_first data H m)
    (arithmeticOneInfinityNormalizedNodeRestriction_node hπ data H m hj u hu false)

/-- The opposite whole source node commutes with the independent target quotient. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedPairIso_restriction_opposite :
    pushout.inr (a m false) (a m true) ≫ v ≫ (G (m + 1)).hom =
      pushout.inr (a m false) (a m true) ≫ (G m).hom ≫ t :=
  normalizedPair_chartSquare
    (arithmeticOneInfinityNormalizedPairRestriction_opposite hπ data H m hj u hu)
    (arithmeticOneInfinityNormalizedPairIso_opposite hπ data H (m + 1) hj u hu)
    (arithmeticOneInfinityNormalizedPairIso_opposite hπ data H m hj u hu)
    (arithmeticOneInfinityNormalizedTargetRestriction_opposite data H m)
    (arithmeticOneInfinityNormalizedNodeRestriction_node hπ data H m hj u hu true)

/-- The two entire source nodes commute with the independent pair quotient. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedPairIso_restriction :
    v ≫ (G (m + 1)).hom = (G m).hom ≫ t := by
  apply pushout.hom_ext
  · exact arithmeticOneInfinityNormalizedPairIso_restriction_first hπ data H m hj u hu
  · exact arithmeticOneInfinityNormalizedPairIso_restriction_opposite hπ data H m hj u hu

/-- The complete pair quotient is the original global quotient on its entire image. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedPairRestriction_global :
    v ≫ k (m + 1) = k m ≫ q := by
  apply pushout.hom_ext
  · rw [arithmeticOneInfinityNormalizedPairRestriction_first_assoc,
      arithmeticOneInfinityNormalizedPairToGlobal_first,
      arithmeticOneInfinityNormalizedPairToGlobal_first_assoc,
      arithmeticOneInfinityNormalizedNodeRestriction_global]
  · rw [arithmeticOneInfinityNormalizedPairRestriction_opposite_assoc,
      arithmeticOneInfinityNormalizedPairToGlobal_opposite,
      arithmeticOneInfinityNormalizedPairToGlobal_opposite_assoc,
      arithmeticOneInfinityNormalizedNodeRestriction_global]

end FLT.Mazur.WeierstrassDividedDepth
