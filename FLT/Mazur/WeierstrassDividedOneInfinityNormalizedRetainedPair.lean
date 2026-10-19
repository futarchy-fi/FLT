/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneInfinityNormalizedRetainedPairIntersection
public import FLT.Mazur.WeierstrassDividedOneInfinityNormalizedRetainedBase

/-!
# Both entire original retained nodes attached to the independent normalized pair

Glue the two exact full retained attachments along their entire common pair.
The independent target is the actual original five-chart union, over its
original base. The retained-1 nodes, terminal and twist normalization remain.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticOneFiniteAtlasIso simultaneousTwistedArithmeticIso
  arithmeticOneFiniteInitialIso arithmeticInitialFactorRatioChart
  arithmeticOneInfinityNormalizedRetainedToGlobal arithmeticOneInfinityNormalizedRetainedSide
  arithmeticOneInfinityNormalizedRetainedToUnion arithmeticOneInfinityNormalizedRetainedPushoutIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "U" => arithmeticOneInfinityNormalizedFullUnion hπ data H m hj u hu
local notation "w" => arithmeticOneInfinityNormalizedRetainedToUnion hπ data H m hj u hu
local notation "r" => arithmeticOneInfinityNormalizedRetainedSide hπ data H m hj u hu
local notation "v" => arithmeticOneInfinityNormalizedTargetLeft data H m
local notation "F" => arithmeticOneInfinityNormalizedFullComparison hπ data H m hj u hu
local notation "G" => arithmeticOneInfinityNormalizedRetainedPushoutIso hπ data H m hj u hu
local notation "g" => arithmeticOneInfinityNormalizedRetainedToGlobal hπ data H m hj u hu
local notation "V" => arithmeticOneInfinityNormalizedRetainedUnion hπ data H m hj u hu
local notation "a" => fun b ↦ pushout.inl (w b) (r b)
local notation "t" => fun b ↦ pushout.inl (v b) (r b)
local notation "p" => arithmeticOneInfinityNormalizedRetainedTargetToBase hπ data H m hj u hu
local notation "B" => arithmeticOneDiagonalSourceToBase hπ data H m hj u hu
local notation "X" => simultaneousTwistedArithmeticStage hπ data H m 1 hj u hu

/-- The independent target attaches both full retained nodes with their exact original twists. -/
def arithmeticOneInfinityNormalizedRetainedPairTarget : Scheme := pushout (t false) (t true)

/-- Both entire retained comparisons glue along the complete original pair comparison. -/
def arithmeticOneInfinityNormalizedRetainedPairIso :
    pushout (a false) (a true) ≅
      arithmeticOneInfinityNormalizedRetainedPairTarget hπ data H m hj u hu :=
  asIso (pushout.map (a false) (a true) (t false) (t true)
    (G false).hom (G true).hom (F).hom
    (arithmeticOneInfinityNormalizedRetainedPushoutIso_pair hπ data H m hj u hu false)
    (arithmeticOneInfinityNormalizedRetainedPushoutIso_pair hπ data H m hj u hu true))

local notation "E" => arithmeticOneInfinityNormalizedRetainedPairIso hπ data H m hj u hu

/-- The full first attachment keeps its complete constructed comparison. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedRetainedPairIso_first :
    pushout.inl (a false) (a true) ≫ (E).hom =
      (G false).hom ≫ pushout.inl (t false) (t true) := pushout.inl_desc _ _ _

/-- The full opposite attachment keeps its complete constructed comparison. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedRetainedPairIso_opposite :
    pushout.inr (a false) (a true) ≫ (E).hom =
      (G true).hom ≫ pushout.inr (t false) (t true) := pushout.inr_desc _ _ _

/-- The complete double attachment has its original global inclusion. -/
def arithmeticOneInfinityNormalizedRetainedPairToGlobal :
    pushout (a false) (a true) ⟶ X :=
  pushout.desc (g false) (g true)
    (arithmeticOneInfinityNormalizedRetainedPair_isPullback hπ data H m hj u hu).w

local notation "j" => arithmeticOneInfinityNormalizedRetainedPairToGlobal hπ data H m hj u hu

instance arithmeticOneInfinityNormalizedRetainedPairToGlobal_isOpenImmersion :
    IsOpenImmersion j :=
  SchemeOpenPushout.coverDesc_isOpenImmersion _ _ _ _
    (arithmeticOneInfinityNormalizedRetainedPair_isPullback hπ data H m hj u hu)

/-- The first full source attachment keeps its original global image. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedRetainedPairToGlobal_first :
    pushout.inl (a false) (a true) ≫ j = g false := pushout.inl_desc _ _ _

/-- The opposite full source attachment keeps its original global image. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedRetainedPairToGlobal_opposite :
    pushout.inr (a false) (a true) ≫ j = g true := pushout.inr_desc _ _ _

/-- The double attachment covers both full retained unions, without adding any other points. -/
theorem arithmeticOneInfinityNormalizedRetainedPairToGlobal_range :
    Set.range j = Set.range (g false) ∪ Set.range (g true) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rcases SchemeOpenPushout.charts_cover (a false) (a true) x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact Or.inl ⟨y, (congrArg (fun h ↦ h y)
        (arithmeticOneInfinityNormalizedRetainedPairToGlobal_first hπ data H m hj u hu)).symm⟩
    · exact Or.inr ⟨y, (congrArg (fun h ↦ h y)
        (arithmeticOneInfinityNormalizedRetainedPairToGlobal_opposite hπ data H m hj u hu)).symm⟩
  · rintro (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact ⟨pushout.inl (a false) (a true) y, congrArg (fun h ↦ h y)
        (arithmeticOneInfinityNormalizedRetainedPairToGlobal_first hπ data H m hj u hu)⟩
    · exact ⟨pushout.inr (a false) (a true) y, congrArg (fun h ↦ h y)
        (arithmeticOneInfinityNormalizedRetainedPairToGlobal_opposite hπ data H m hj u hu)⟩

/-- The actual original five-chart union contains the full pair and both whole retained nodes. -/
def arithmeticOneInfinityNormalizedRetainedPairUnion : (X).Opens := V false ⊔ V true

local notation "W₀" => arithmeticOneInfinityNormalizedRetainedPairUnion hπ data H m hj u hu

/-- The full double attachment is precisely the actual original five-chart open union. -/
def arithmeticOneInfinityNormalizedRetainedPairUnionIso :
    pushout (a false) (a true) ≅ (W₀).toScheme :=
  IsOpenImmersion.isoOfRangeEq j (W₀).ι (by
    rw [Scheme.Opens.range_ι, arithmeticOneInfinityNormalizedRetainedPairToGlobal_range,
      arithmeticOneInfinityNormalizedRetainedToGlobal_range,
      arithmeticOneInfinityNormalizedRetainedToGlobal_range, Scheme.Opens.range_ι]
    rfl)

/-- The full union identification preserves its original global inclusion. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedRetainedPairUnionIso_global :
    (arithmeticOneInfinityNormalizedRetainedPairUnionIso hπ data H m hj u hu).hom ≫
      (W₀).ι = j := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- Both exact whole-node attachments compare with the actual five-chart source union. -/
def arithmeticOneInfinityNormalizedRetainedPairComparison :
    (W₀).toScheme ≅ arithmeticOneInfinityNormalizedRetainedPairTarget hπ data H m hj u hu :=
  (arithmeticOneInfinityNormalizedRetainedPairUnionIso hπ data H m hj u hu).symm ≪≫ E

/-- The full double-attachment target retains its original arithmetic coefficient base. -/
def arithmeticOneInfinityNormalizedRetainedPairTargetToBase :
    arithmeticOneInfinityNormalizedRetainedPairTarget hπ data H m hj u hu ⟶
      Spec (.of (Quotient R π m)) :=
  pushout.desc (p false) (p true) (by
    rw [arithmeticOneInfinityNormalizedRetainedTargetToBase_pair,
      arithmeticOneInfinityNormalizedRetainedTargetToBase_pair])

local notation "q" => arithmeticOneInfinityNormalizedRetainedPairTargetToBase hπ data H m hj u hu

/-- The whole double-attachment comparison preserves the original global base. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedRetainedPairIso_base :
    (E).hom ≫ q = j ≫ B := by
  apply pushout.hom_ext
  · rw [arithmeticOneInfinityNormalizedRetainedPairIso_first_assoc]
    change (G false).hom ≫ pushout.inl (t false) (t true) ≫
      pushout.desc (p false) (p true) _ = _
    rw [pushout.inl_desc, arithmeticOneInfinityNormalizedRetainedPushoutIso_base,
      arithmeticOneInfinityNormalizedRetainedPairToGlobal_first_assoc]
  · rw [arithmeticOneInfinityNormalizedRetainedPairIso_opposite_assoc]
    change (G true).hom ≫ pushout.inr (t false) (t true) ≫
      pushout.desc (p false) (p true) _ = _
    rw [pushout.inr_desc, arithmeticOneInfinityNormalizedRetainedPushoutIso_base,
      arithmeticOneInfinityNormalizedRetainedPairToGlobal_opposite_assoc]

/-- The complete five-chart source comparison preserves the original base. -/
@[reassoc] theorem arithmeticOneInfinityNormalizedRetainedPairComparison_base :
    (arithmeticOneInfinityNormalizedRetainedPairComparison hπ data H m hj u hu).hom ≫ q =
      (W₀).ι ≫ B := by
  apply (cancel_epi
    (arithmeticOneInfinityNormalizedRetainedPairUnionIso hπ data H m hj u hu).hom).mp
  simp only [arithmeticOneInfinityNormalizedRetainedPairComparison, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
    arithmeticOneInfinityNormalizedRetainedPairIso_base,
    arithmeticOneInfinityNormalizedRetainedPairUnionIso_global_assoc]

end FLT.Mazur.WeierstrassDividedDepth
