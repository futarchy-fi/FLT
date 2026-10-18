/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedPair

/-!
# The actual three-chart source union is the normalized two-node target

The full infinity and both original initial opens have a constructed comparison
isomorphism. The two retained-edge attachments remain separate obligations.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart arithmeticZeroFiniteAtlasIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "N" => arithmeticInitialFactorRatioChart π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "P" => arithmeticFactorRatioOverlapParameter π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "E" => arithmeticZeroDiagonalInitialOpenIso hπ data H m hj u hu
local notation "T" => arithmeticZeroDiagonalInitialTotalNodeIso hπ data H m hj u hu
local notation "F" => arithmeticZeroDiagonalInitialFactorRatio hπ data H m hj u hu
local notation "l" => arithmeticZeroDiagonalInitialOverlap hπ data H m hj u hu
local notation "i" => arithmeticZeroDiagonalOverlapToInfinity hπ data H m hj u hu
local notation "V" => arithmeticZeroDiagonalInfinityParameterIso hπ data H m hj u hu
local notation "A" => arithmeticZeroFiniteAtlasObject hπ data H m m hj u hu

local notation "f" => arithmeticZeroInfinityNormalizedInitial hπ data H m hj u hu
local notation "g" => arithmeticZeroInfinityNormalizedBoundary hπ data H m hj u hu
local notation "P₀" => polynomialNodeOverlapInclusion
  (W.map (algebraMap R Q)) (algebraMap R Q (π ^ 1))

local notation "c" => arithmeticZeroFiniteAtlasChart hπ data H m m hj u hu
local notation "X" => simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu

local notation "j" => arithmeticZeroInfinityNormalizedToGlobal hπ data H m hj u hu
local notation "a" => fun b ↦ pushout.inl i (l b)

local notation "r" => rightBranchOpen Q τ
local notation "r'" => Iso.hom (edgeInversion Q) ≫ r
local notation "e" => arithmeticZeroInfinityNormalizedNodeIso hπ data H m hj u hu

local notation "S" => arithmeticZeroInfinityNormalizedSourcePair hπ data H m hj u hu
local notation "G" => arithmeticZeroInfinityNormalizedPairIso hπ data H m hj u hu

/-- The whole two-node source presentation maps into the actual original global stage. -/
def arithmeticZeroInfinityNormalizedPairToGlobal : S ⟶ X :=
  pushout.desc (j false) (j true)
    (arithmeticZeroInfinityNormalizedNodes_isPullback hπ data H m hj u hu).w

local notation "k" => arithmeticZeroInfinityNormalizedPairToGlobal hπ data H m hj u hu

instance arithmeticZeroInfinityNormalizedPairToGlobal_isOpenImmersion : IsOpenImmersion k :=
  SchemeOpenPushout.coverDesc_isOpenImmersion (a false) (a true) (j false) (j true)
    (arithmeticZeroInfinityNormalizedNodes_isPullback hπ data H m hj u hu)

/-- The full first source node retains its actual global inclusion. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedPairToGlobal_first :
    pushout.inl (a false) (a true) ≫ k = j false := pushout.inl_desc _ _ _

/-- The full opposite source node retains its actual global inclusion. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedPairToGlobal_opposite :
    pushout.inr (a false) (a true) ≫ k = j true := pushout.inr_desc _ _ _

/-- The full source presentation has exactly the union of both complete source nodes. -/
theorem arithmeticZeroInfinityNormalizedPairToGlobal_range :
    Set.range k = Set.range (j false) ∪ Set.range (j true) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rcases SchemeOpenPushout.charts_cover (a false) (a true) x with ⟨v, rfl⟩ | ⟨v, rfl⟩
    · exact Or.inl ⟨v, (congrArg (fun h ↦ h v)
        (arithmeticZeroInfinityNormalizedPairToGlobal_first hπ data H m hj u hu)).symm⟩
    · exact Or.inr ⟨v, (congrArg (fun h ↦ h v)
        (arithmeticZeroInfinityNormalizedPairToGlobal_opposite hπ data H m hj u hu)).symm⟩
  · rintro (⟨v, rfl⟩ | ⟨v, rfl⟩)
    · exact ⟨pushout.inl (a false) (a true) v, congrArg (fun h ↦ h v)
        (arithmeticZeroInfinityNormalizedPairToGlobal_first hπ data H m hj u hu)⟩
    · exact ⟨pushout.inr (a false) (a true) v, congrArg (fun h ↦ h v)
        (arithmeticZeroInfinityNormalizedPairToGlobal_opposite hπ data H m hj u hu)⟩

/-- The actual three-chart open union of the original corrected arithmetic stage. -/
def arithmeticZeroInfinityNormalizedFullUnion : (X).Opens :=
  arithmeticZeroInfinityNormalizedUnion hπ data H m hj u hu false ⊔
    arithmeticZeroInfinityNormalizedUnion hπ data H m hj u hu true

local notation "U" => arithmeticZeroInfinityNormalizedFullUnion hπ data H m hj u hu

/-- The whole node-pair presentation is precisely the actual original three-chart union. -/
def arithmeticZeroInfinityNormalizedFullUnionIso : S ≅ (U).toScheme :=
  IsOpenImmersion.isoOfRangeEq k (U).ι (by
    rw [Scheme.Opens.range_ι, arithmeticZeroInfinityNormalizedPairToGlobal_range,
      arithmeticZeroInfinityNormalizedToGlobal_range,
      arithmeticZeroInfinityNormalizedToGlobal_range]
    rfl)

local notation "J" => arithmeticZeroInfinityNormalizedFullUnionIso hπ data H m hj u hu

/-- The complete actual source union is the independent two-node normalized target. -/
def arithmeticZeroInfinityNormalizedFullComparison :
    (U).toScheme ≅ arithmeticZeroInfinityNormalizedTargetPair data H m := (J).symm ≪≫ G

/-- The source-union presentation retains its original global inclusion. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedFullUnionIso_global :
    (J).hom ≫ (U).ι = k := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The whole comparison recovers the constructed full two-node pushout isomorphism. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedFullComparison_transport :
    (J).hom ≫ (arithmeticZeroInfinityNormalizedFullComparison hπ data H m hj u hu).hom =
      (G).hom := by
  simp only [arithmeticZeroInfinityNormalizedFullComparison, Iso.trans_hom,
    Iso.symm_hom, Iso.hom_inv_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
