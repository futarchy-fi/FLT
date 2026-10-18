/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedRetainedIntersection

/-!
# Attaching an entire original retained node to the independent normalized pair

Glue along the exact full retained-side substitution. The resulting independent
pushout is isomorphic to the actual four-chart source union. This construction
does not replace the retained parameter by a standard reciprocal boundary.
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
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "c" => arithmeticZeroDiagonalAtlasChart hπ data H m hj u hu
local notation "U" => arithmeticZeroInfinityNormalizedFullUnion hπ data H m hj u hu
local notation "w" => arithmeticZeroInfinityNormalizedRetainedToUnion hπ data H m hj u hu
local notation "r" => arithmeticZeroInfinityNormalizedRetainedSide hπ data H m hj u hu
local notation "v" => arithmeticZeroInfinityNormalizedTargetLeft data H m
local notation "F" => arithmeticZeroInfinityNormalizedFullComparison hπ data H m hj u hu
local notation "X" => simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu

/-- Attach the full original retained node to the independent pair using its exact parameter. -/
def arithmeticZeroInfinityNormalizedRetainedTarget (b : Bool) : Scheme :=
  pushout (v b) (r b)

/-- The full pair comparison extends across the entire retained node by the identity. -/
def arithmeticZeroInfinityNormalizedRetainedPushoutIso (b : Bool) :
    pushout (w b) (r b) ≅ arithmeticZeroInfinityNormalizedRetainedTarget hπ data H m hj u hu b :=
  asIso (pushout.map (w b) (r b) (v b) (r b) (F).hom (𝟙 _) (𝟙 _)
    (by rw [arithmeticZeroInfinityNormalizedRetainedToUnion_comparison, Category.id_comp])
    (by rw [Category.comp_id, Category.id_comp]))

local notation "G" => arithmeticZeroInfinityNormalizedRetainedPushoutIso hπ data H m hj u hu

/-- The extended comparison retains the complete original pair comparison. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPushoutIso_pair (b : Bool) :
    pushout.inl (w b) (r b) ≫ (G b).hom = (F).hom ≫ pushout.inl (v b) (r b) :=
  pushout.inl_desc _ _ _

/-- The extended comparison preserves every point of the full original retained node. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedPushoutIso_retained (b : Bool) :
    pushout.inr (w b) (r b) ≫ (G b).hom = pushout.inr (v b) (r b) := by
  change pushout.inr (w b) (r b) ≫ (G b).hom = 𝟙 _ ≫ pushout.inr (v b) (r b)
  exact pushout.inr_desc _ _ _

/-- The complete attachment maps to the actual original arithmetic stage. -/
def arithmeticZeroInfinityNormalizedRetainedToGlobal (b : Bool) :
    pushout (w b) (r b) ⟶ X :=
  pushout.desc (U).ι (c (.retained ⟨0, by omega⟩ b))
    (arithmeticZeroInfinityNormalizedRetained_isPullback hπ data H m hj u hu b).w

local notation "g" => arithmeticZeroInfinityNormalizedRetainedToGlobal hπ data H m hj u hu

instance arithmeticZeroInfinityNormalizedRetainedToGlobal_isOpenImmersion (b : Bool) :
    IsOpenImmersion (g b) :=
  SchemeOpenPushout.coverDesc_isOpenImmersion _ _ _ _
    (arithmeticZeroInfinityNormalizedRetained_isPullback hπ data H m hj u hu b)

/-- The attachment preserves the original full pair inclusion. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedToGlobal_pair (b : Bool) :
    pushout.inl (w b) (r b) ≫ g b = (U).ι := pushout.inl_desc _ _ _

/-- The attachment preserves the original full retained inclusion. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedToGlobal_retained (b : Bool) :
    pushout.inr (w b) (r b) ≫ g b = c (.retained ⟨0, by omega⟩ b) := pushout.inr_desc _ _ _

/-- The full attachment covers exactly the original pair and its whole retained node. -/
theorem arithmeticZeroInfinityNormalizedRetainedToGlobal_range (b : Bool) :
    Set.range (g b) = Set.range (U).ι ∪ Set.range (c (.retained ⟨0, by omega⟩ b)) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rcases SchemeOpenPushout.charts_cover (w b) (r b) x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact Or.inl ⟨y, (congrArg (fun h ↦ h y)
        (arithmeticZeroInfinityNormalizedRetainedToGlobal_pair hπ data H m hj u hu b)).symm⟩
    · exact Or.inr ⟨y, (congrArg (fun h ↦ h y)
        (arithmeticZeroInfinityNormalizedRetainedToGlobal_retained hπ data H m hj u hu b)).symm⟩
  · rintro (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact ⟨pushout.inl (w b) (r b) y, congrArg (fun h ↦ h y)
        (arithmeticZeroInfinityNormalizedRetainedToGlobal_pair hπ data H m hj u hu b)⟩
    · exact ⟨pushout.inr (w b) (r b) y, congrArg (fun h ↦ h y)
        (arithmeticZeroInfinityNormalizedRetainedToGlobal_retained hπ data H m hj u hu b)⟩

/-- The full original four-chart open union, for either retained label. -/
def arithmeticZeroInfinityNormalizedRetainedUnion (b : Bool) : (X).Opens :=
  U ⊔ (c (.retained ⟨0, by omega⟩ b)).opensRange

local notation "V" => arithmeticZeroInfinityNormalizedRetainedUnion hπ data H m hj u hu

/-- The full source attachment presents its actual original open union. -/
def arithmeticZeroInfinityNormalizedRetainedUnionIso (b : Bool) :
    pushout (w b) (r b) ≅ (V b).toScheme :=
  IsOpenImmersion.isoOfRangeEq (g b) (V b).ι (by
    rw [Scheme.Opens.range_ι, arithmeticZeroInfinityNormalizedRetainedToGlobal_range,
      Scheme.Opens.range_ι]
    rfl)

/-- The independent attached pair compares with the entire actual four-chart source union. -/
def arithmeticZeroInfinityNormalizedRetainedComparison (b : Bool) :
    (V b).toScheme ≅ arithmeticZeroInfinityNormalizedRetainedTarget hπ data H m hj u hu b :=
  (arithmeticZeroInfinityNormalizedRetainedUnionIso hπ data H m hj u hu b).symm ≪≫ G b

/-- The actual union identification retains its original full global inclusion. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedRetainedUnionIso_global (b : Bool) :
    (arithmeticZeroInfinityNormalizedRetainedUnionIso hπ data H m hj u hu b).hom ≫
      (V b).ι = g b := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end FLT.Mazur.WeierstrassDividedDepth
