/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneInfinityNormalizedIntersection

/-!
# Gluing both full normalized nodes along the exact infinity parameter

The independent two-node target uses the standard reciprocal edge. Its
comparison is an isomorphism from the full source pushout, not an equation
that assumes the old accumulated transition is inversion.
-/

@[expose] public noncomputable section
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
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "N" => arithmeticInitialFactorRatioChart π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "P" => arithmeticFactorRatioOverlapParameter π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "E" => arithmeticOneDiagonalInitialTotalOpenIso hπ data H m hj u hu
local notation "T" => arithmeticOneDiagonalInitialTotalNodeIso hπ data H m hj u hu
local notation "F" => arithmeticOneDiagonalInitialFactorRatio hπ data H m hj u hu
local notation "l" => arithmeticOneDiagonalInitialOverlap hπ data H m hj u hu
local notation "i" => arithmeticOneDiagonalOverlapToInfinity hπ data H m hj u hu
local notation "V" => arithmeticOneDiagonalInfinityParameterIso hπ data H m hj u hu
local notation "A" => arithmeticOneFiniteAtlasObject hπ data H m m hj u hu

local notation "f" => arithmeticOneInfinityNormalizedInitial hπ data H m hj u hu
local notation "g" => arithmeticOneInfinityNormalizedBoundary hπ data H m hj u hu
local notation "P₀" => polynomialNodeOverlapInclusion
  (W.map (algebraMap R Q)) (algebraMap R Q (π ^ 1))

local notation "c" => arithmeticOneFiniteAtlasChart hπ data H m m hj u hu
local notation "X" => simultaneousTwistedArithmeticStage hπ data H m 1 hj u hu

local notation "j" => arithmeticOneInfinityNormalizedToGlobal hπ data H m hj u hu
local notation "a" => fun b ↦ pushout.inl i (l b)

local notation "r" => rightBranchOpen Q τ
local notation "r'" => Iso.hom (edgeInversion Q) ≫ r
local notation "e" => arithmeticOneInfinityNormalizedNodeIso hπ data H m hj u hu

/-- Glue the two actual source node unions along their entire common infinity chart. -/
def arithmeticOneInfinityNormalizedSourcePair : Scheme := pushout (a false) (a true)

/-- The independent full two-node target uses the original smoothing and reciprocal edge. -/
def arithmeticOneInfinityNormalizedTargetPair : Scheme := pushout r r'

/-- The two whole-node comparisons glue through the full original infinity isomorphism. -/
def arithmeticOneInfinityNormalizedPairIso :
    arithmeticOneInfinityNormalizedSourcePair hπ data H m hj u hu ≅
      arithmeticOneInfinityNormalizedTargetPair data H m :=
  asIso (pushout.map (a false) (a true) r r' (e false).hom (e true).hom (V).hom
    (by rw [arithmeticOneInfinityNormalizedNodeIso_infinity]
        simp only [arithmeticOneInfinityNormalizedBoundary, Bool.false_eq_true,
          ↓reduceIte, Category.id_comp])
    (by rw [arithmeticOneInfinityNormalizedNodeIso_infinity]
        simp only [arithmeticOneInfinityNormalizedBoundary, ↓reduceIte]))

local notation "Z" => arithmeticOneInfinityNormalizedTargetPair data H m
local notation "G" => arithmeticOneInfinityNormalizedPairIso hπ data H m hj u hu

/-- The pair isomorphism retains the entire first node comparison. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedPairIso_first :
    pushout.inl (a false) (a true) ≫ (G).hom = (e false).hom ≫ pushout.inl r r' :=
  pushout.inl_desc _ _ _

/-- The pair isomorphism retains the entire opposite node comparison. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedPairIso_opposite :
    pushout.inr (a false) (a true) ≫ (G).hom = (e true).hom ≫ pushout.inr r r' :=
  pushout.inr_desc _ _ _

/-- Both full original initial charts enter the independent normalized node pair. -/
def arithmeticOneInfinityNormalizedPairInitial (b : Bool) : A (.initial b) ⟶ Z :=
  f b ≫ (if b then pushout.inr r r' else pushout.inl r r')

/-- The whole original infinity chart enters the common standard edge of the node pair. -/
def arithmeticOneInfinityNormalizedPairInfinity : A .infinity ⟶ Z :=
  (V).hom ≫ r ≫ pushout.inl r r'

local notation "f'" => arithmeticOneInfinityNormalizedPairInitial hπ data H m hj u hu
local notation "g'" => arithmeticOneInfinityNormalizedPairInfinity hπ data H m hj u hu

omit [IsBezout R] in
/-- The actual full original infinity parameter agrees on the two full target nodes. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedPair_boundary (b : Bool) :
    g b ≫ (if b then pushout.inr r r' else pushout.inl r r') = g' := by
  cases b
  · simp only [arithmeticOneInfinityNormalizedBoundary,
      arithmeticOneInfinityNormalizedPairInfinity, Bool.false_eq_true, ↓reduceIte,
      Category.id_comp, Category.assoc]
  · simp only [arithmeticOneInfinityNormalizedBoundary,
      arithmeticOneInfinityNormalizedPairInfinity, ↓reduceIte, Category.assoc]
    have hc : r ≫ pushout.inl r r' = r' ≫ pushout.inr r r' := pushout.condition
    simpa only [Category.assoc] using congrArg ((V).hom ≫ ·) hc.symm

/-- Both full initial/infinity equations hold in the independent normalized target pair. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedPair_overlap (b : Bool) :
    i ≫ g' = l b ≫ f' b := by
  rw [← arithmeticOneInfinityNormalizedPair_boundary hπ data H m hj u hu b,
    ← Category.assoc, arithmeticOneInfinityNormalized_compatible, Category.assoc]
  rfl

/-- The full original initial-pair gluing equation now holds without a Laurent assumption. -/
theorem arithmeticOneInfinityNormalizedPair_initial_pair :
    l false ≫ f' false = l true ≫ f' true := by
  rw [← arithmeticOneInfinityNormalizedPair_overlap,
    ← arithmeticOneInfinityNormalizedPair_overlap]

end FLT.Mazur.WeierstrassDividedDepth
