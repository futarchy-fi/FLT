/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedRetainedPairIntersection

/-!
# Both entire original retained nodes attached to the independent normalized pair

Glue the two exact full retained attachments along their entire common pair.
The independent target is the actual original five-chart union, over its
original base. The common terminal and standardization of the twists remain.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteAtlasIso simultaneousTwistedArithmeticIso
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart
  arithmeticZeroInfinityNormalizedRetainedToGlobal arithmeticZeroInfinityNormalizedRetainedSide
  arithmeticZeroInfinityNormalizedRetainedToUnion arithmeticZeroInfinityNormalizedRetainedPushoutIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "U" => arithmeticZeroInfinityNormalizedFullUnion hπ data H m hj u hu
local notation "w" => arithmeticZeroInfinityNormalizedRetainedToUnion hπ data H m hj u hu
local notation "r" => arithmeticZeroInfinityNormalizedRetainedSide hπ data H m hj u hu
local notation "v" => arithmeticZeroInfinityNormalizedTargetLeft data H m
local notation "F" => arithmeticZeroInfinityNormalizedFullComparison hπ data H m hj u hu
local notation "G" => arithmeticZeroInfinityNormalizedRetainedPushoutIso hπ data H m hj u hu
local notation "g" => arithmeticZeroInfinityNormalizedRetainedToGlobal hπ data H m hj u hu
local notation "V" => arithmeticZeroInfinityNormalizedRetainedUnion hπ data H m hj u hu
local notation "a" => fun b ↦ pushout.inl (w b) (r b)
local notation "t" => fun b ↦ pushout.inl (v b) (r b)
local notation "p" => arithmeticZeroInfinityNormalizedRetainedTargetToBase hπ data H m hj u hu
local notation "B" => arithmeticZeroDiagonalSourceToBase hπ data H m hj u hu
local notation "X" => simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu

/-- The independent target attaches both full retained nodes with their exact original twists. -/
def arithmeticZeroInfinityNormalizedRetainedPairTarget : Scheme := pushout (t false) (t true)

/-- Both entire retained comparisons glue along the complete original pair comparison. -/
def arithmeticZeroInfinityNormalizedRetainedPairIso :
    pushout (a false) (a true) ≅
      arithmeticZeroInfinityNormalizedRetainedPairTarget hπ data H m hj u hu :=
  asIso (pushout.map (a false) (a true) (t false) (t true)
    (G false).hom (G true).hom (F).hom
    (arithmeticZeroInfinityNormalizedRetainedPushoutIso_pair hπ data H m hj u hu false)
    (arithmeticZeroInfinityNormalizedRetainedPushoutIso_pair hπ data H m hj u hu true))

local notation "E" => arithmeticZeroInfinityNormalizedRetainedPairIso hπ data H m hj u hu

/-- The full first attachment keeps its complete constructed comparison. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPairIso_first :
    pushout.inl (a false) (a true) ≫ (E).hom =
      (G false).hom ≫ pushout.inl (t false) (t true) := pushout.inl_desc _ _ _

/-- The full opposite attachment keeps its complete constructed comparison. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPairIso_opposite :
    pushout.inr (a false) (a true) ≫ (E).hom =
      (G true).hom ≫ pushout.inr (t false) (t true) := pushout.inr_desc _ _ _

/-- The complete double attachment has its original global inclusion. -/
def arithmeticZeroInfinityNormalizedRetainedPairToGlobal :
    pushout (a false) (a true) ⟶ X :=
  pushout.desc (g false) (g true)
    (arithmeticZeroInfinityNormalizedRetainedPair_isPullback hπ data H m hj u hu).w

local notation "j" => arithmeticZeroInfinityNormalizedRetainedPairToGlobal hπ data H m hj u hu

instance arithmeticZeroInfinityNormalizedRetainedPairToGlobal_isOpenImmersion :
    IsOpenImmersion j :=
  SchemeOpenPushout.coverDesc_isOpenImmersion _ _ _ _
    (arithmeticZeroInfinityNormalizedRetainedPair_isPullback hπ data H m hj u hu)

/-- The first full source attachment keeps its original global image. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPairToGlobal_first :
    pushout.inl (a false) (a true) ≫ j = g false := pushout.inl_desc _ _ _

/-- The opposite full source attachment keeps its original global image. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPairToGlobal_opposite :
    pushout.inr (a false) (a true) ≫ j = g true := pushout.inr_desc _ _ _

/-- The double attachment covers both full retained unions, without adding any other points. -/
theorem arithmeticZeroInfinityNormalizedRetainedPairToGlobal_range :
    Set.range j = Set.range (g false) ∪ Set.range (g true) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rcases SchemeOpenPushout.charts_cover (a false) (a true) x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact Or.inl ⟨y, (congrArg (fun h ↦ h y)
        (arithmeticZeroInfinityNormalizedRetainedPairToGlobal_first hπ data H m hj u hu)).symm⟩
    · exact Or.inr ⟨y, (congrArg (fun h ↦ h y)
        (arithmeticZeroInfinityNormalizedRetainedPairToGlobal_opposite hπ data H m hj u hu)).symm⟩
  · rintro (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact ⟨pushout.inl (a false) (a true) y, congrArg (fun h ↦ h y)
        (arithmeticZeroInfinityNormalizedRetainedPairToGlobal_first hπ data H m hj u hu)⟩
    · exact ⟨pushout.inr (a false) (a true) y, congrArg (fun h ↦ h y)
        (arithmeticZeroInfinityNormalizedRetainedPairToGlobal_opposite hπ data H m hj u hu)⟩

/-- The actual original five-chart union contains the full pair and both whole retained nodes. -/
def arithmeticZeroInfinityNormalizedRetainedPairUnion : (X).Opens := V false ⊔ V true

local notation "W₀" => arithmeticZeroInfinityNormalizedRetainedPairUnion hπ data H m hj u hu

/-- The full double attachment is precisely the actual original five-chart open union. -/
def arithmeticZeroInfinityNormalizedRetainedPairUnionIso :
    pushout (a false) (a true) ≅ (W₀).toScheme :=
  IsOpenImmersion.isoOfRangeEq j (W₀).ι (by
    rw [Scheme.Opens.range_ι, arithmeticZeroInfinityNormalizedRetainedPairToGlobal_range,
      arithmeticZeroInfinityNormalizedRetainedToGlobal_range,
      arithmeticZeroInfinityNormalizedRetainedToGlobal_range, Scheme.Opens.range_ι]
    rfl)

/-- The full union identification preserves its original global inclusion. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPairUnionIso_global :
    (arithmeticZeroInfinityNormalizedRetainedPairUnionIso hπ data H m hj u hu).hom ≫
      (W₀).ι = j := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- Both exact whole-node attachments compare with the actual five-chart source union. -/
def arithmeticZeroInfinityNormalizedRetainedPairComparison :
    (W₀).toScheme ≅ arithmeticZeroInfinityNormalizedRetainedPairTarget hπ data H m hj u hu :=
  (arithmeticZeroInfinityNormalizedRetainedPairUnionIso hπ data H m hj u hu).symm ≪≫ E

/-- The full double-attachment target retains its original arithmetic coefficient base. -/
def arithmeticZeroInfinityNormalizedRetainedPairTargetToBase :
    arithmeticZeroInfinityNormalizedRetainedPairTarget hπ data H m hj u hu ⟶
      Spec (.of (Quotient R π m)) :=
  pushout.desc (p false) (p true) (by
    rw [arithmeticZeroInfinityNormalizedRetainedTargetToBase_pair,
      arithmeticZeroInfinityNormalizedRetainedTargetToBase_pair])

local notation "q" => arithmeticZeroInfinityNormalizedRetainedPairTargetToBase hπ data H m hj u hu

/-- The whole double-attachment comparison preserves the original global base. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPairIso_base :
    (E).hom ≫ q = j ≫ B := by
  apply pushout.hom_ext
  · rw [arithmeticZeroInfinityNormalizedRetainedPairIso_first_assoc]
    change (G false).hom ≫ pushout.inl (t false) (t true) ≫
      pushout.desc (p false) (p true) _ = _
    rw [pushout.inl_desc, arithmeticZeroInfinityNormalizedRetainedPushoutIso_base,
      arithmeticZeroInfinityNormalizedRetainedPairToGlobal_first_assoc]
  · rw [arithmeticZeroInfinityNormalizedRetainedPairIso_opposite_assoc]
    change (G true).hom ≫ pushout.inr (t false) (t true) ≫
      pushout.desc (p false) (p true) _ = _
    rw [pushout.inr_desc, arithmeticZeroInfinityNormalizedRetainedPushoutIso_base,
      arithmeticZeroInfinityNormalizedRetainedPairToGlobal_opposite_assoc]

/-- The complete five-chart source comparison preserves the original base. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPairComparison_base :
    (arithmeticZeroInfinityNormalizedRetainedPairComparison hπ data H m hj u hu).hom ≫ q =
      (W₀).ι ≫ B := by
  apply (cancel_epi
    (arithmeticZeroInfinityNormalizedRetainedPairUnionIso hπ data H m hj u hu).hom).mp
  simp only [arithmeticZeroInfinityNormalizedRetainedPairComparison, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
    arithmeticZeroInfinityNormalizedRetainedPairIso_base,
    arithmeticZeroInfinityNormalizedRetainedPairUnionIso_global_assoc]

end FLT.Mazur.WeierstrassDividedDepth
