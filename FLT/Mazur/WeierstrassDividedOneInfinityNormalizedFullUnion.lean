/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneInfinityNormalizedPair

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

local notation "S" => arithmeticOneInfinityNormalizedSourcePair hπ data H m hj u hu
local notation "G" => arithmeticOneInfinityNormalizedPairIso hπ data H m hj u hu

/-- The whole two-node source presentation maps into the actual original global stage. -/
def arithmeticOneInfinityNormalizedPairToGlobal : S ⟶ X :=
  pushout.desc (j false) (j true)
    (arithmeticOneInfinityNormalizedNodes_isPullback hπ data H m hj u hu).w

local notation "k" => arithmeticOneInfinityNormalizedPairToGlobal hπ data H m hj u hu

instance arithmeticOneInfinityNormalizedPairToGlobal_isOpenImmersion : IsOpenImmersion k :=
  SchemeOpenPushout.coverDesc_isOpenImmersion (a false) (a true) (j false) (j true)
    (arithmeticOneInfinityNormalizedNodes_isPullback hπ data H m hj u hu)

/-- The full first source node retains its actual global inclusion. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedPairToGlobal_first :
    pushout.inl (a false) (a true) ≫ k = j false := pushout.inl_desc _ _ _

/-- The full opposite source node retains its actual global inclusion. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedPairToGlobal_opposite :
    pushout.inr (a false) (a true) ≫ k = j true := pushout.inr_desc _ _ _

/-- The full source presentation has exactly the union of both complete source nodes. -/
theorem arithmeticOneInfinityNormalizedPairToGlobal_range :
    Set.range k = Set.range (j false) ∪ Set.range (j true) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rcases SchemeOpenPushout.charts_cover (a false) (a true) x with ⟨v, rfl⟩ | ⟨v, rfl⟩
    · exact Or.inl ⟨v, (congrArg (fun h ↦ h v)
        (arithmeticOneInfinityNormalizedPairToGlobal_first hπ data H m hj u hu)).symm⟩
    · exact Or.inr ⟨v, (congrArg (fun h ↦ h v)
        (arithmeticOneInfinityNormalizedPairToGlobal_opposite hπ data H m hj u hu)).symm⟩
  · rintro (⟨v, rfl⟩ | ⟨v, rfl⟩)
    · exact ⟨pushout.inl (a false) (a true) v, congrArg (fun h ↦ h v)
        (arithmeticOneInfinityNormalizedPairToGlobal_first hπ data H m hj u hu)⟩
    · exact ⟨pushout.inr (a false) (a true) v, congrArg (fun h ↦ h v)
        (arithmeticOneInfinityNormalizedPairToGlobal_opposite hπ data H m hj u hu)⟩

/-- The actual three-chart open union of the original corrected arithmetic stage. -/
def arithmeticOneInfinityNormalizedFullUnion : (X).Opens :=
  arithmeticOneInfinityNormalizedUnion hπ data H m hj u hu false ⊔
    arithmeticOneInfinityNormalizedUnion hπ data H m hj u hu true

local notation "U" => arithmeticOneInfinityNormalizedFullUnion hπ data H m hj u hu

/-- The whole node-pair presentation is precisely the actual original three-chart union. -/
def arithmeticOneInfinityNormalizedFullUnionIso : S ≅ (U).toScheme :=
  IsOpenImmersion.isoOfRangeEq k (U).ι (by
    rw [Scheme.Opens.range_ι, arithmeticOneInfinityNormalizedPairToGlobal_range,
      arithmeticOneInfinityNormalizedToGlobal_range,
      arithmeticOneInfinityNormalizedToGlobal_range]
    rfl)

local notation "J" => arithmeticOneInfinityNormalizedFullUnionIso hπ data H m hj u hu

/-- The complete actual source union is the independent two-node normalized target. -/
def arithmeticOneInfinityNormalizedFullComparison :
    (U).toScheme ≅ arithmeticOneInfinityNormalizedTargetPair data H m := (J).symm ≪≫ G

/-- The source-union presentation retains its original global inclusion. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedFullUnionIso_global :
    (J).hom ≫ (U).ι = k := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The whole comparison recovers the constructed full two-node pushout isomorphism. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedFullComparison_transport :
    (J).hom ≫ (arithmeticOneInfinityNormalizedFullComparison hπ data H m hj u hu).hom =
      (G).hom := by
  simp only [arithmeticOneInfinityNormalizedFullComparison, Iso.trans_hom,
    Iso.symm_hom, Iso.hom_inv_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
