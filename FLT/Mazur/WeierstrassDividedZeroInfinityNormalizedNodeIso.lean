/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedCover

/-!
# Both actual full initial/infinity unions are normalized nodes

The complete D(q) pushouts identify the actual original source unions with
whole nodes. Their common infinity chart keeps reciprocal full parameters.
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

/-- Each full original initial/infinity pair is glued along its complete D(q). -/
def arithmeticZeroInfinityNormalizedPushout (b : Bool) : Scheme := pushout i (l b)

/-- Both original full pairs identify with whole nodes having the original smoothing. -/
def arithmeticZeroInfinityNormalizedNodeIso (b : Bool) :
    arithmeticZeroInfinityNormalizedPushout hπ data H m hj u hu b ≅
      PolygonSmoothing.chart Q τ :=
  SchemeOpenPushout.coverIso i (l b) (g b) (f b)
    (arithmeticZeroInfinityNormalized_isPullback hπ data H m hj u hu b)
    (fun x ↦ (arithmeticZeroInfinityNormalized_cover hπ data H m hj u hu b x).symm)

local notation "e" => arithmeticZeroInfinityNormalizedNodeIso hπ data H m hj u hu

/-- The whole node isomorphism retains the original full infinity chart. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedNodeIso_infinity (b : Bool) :
    pushout.inl i (l b) ≫ (e b).hom = g b :=
  SchemeOpenPushout.inl_coverIso ..

/-- The whole node isomorphism retains the full original initial open. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedNodeIso_initial (b : Bool) :
    pushout.inr i (l b) ≫ (e b).hom = f b :=
  SchemeOpenPushout.inr_coverIso ..

/-- Each full original pair enters the actual corrected arithmetic stage. -/
def arithmeticZeroInfinityNormalizedToGlobal (b : Bool) :
    arithmeticZeroInfinityNormalizedPushout hπ data H m hj u hu b ⟶ X :=
  pushout.desc (c .infinity) (c (.initial b))
    (arithmeticZeroDiagonalAtlas_initial_infinity_isPullback hπ data H m hj u hu b).w

local notation "j" => arithmeticZeroInfinityNormalizedToGlobal hπ data H m hj u hu

instance arithmeticZeroInfinityNormalizedToGlobal_isOpenImmersion (b : Bool) :
    IsOpenImmersion (j b) :=
  SchemeOpenPushout.coverDesc_isOpenImmersion i (l b) (c .infinity) (c (.initial b))
    (arithmeticZeroDiagonalAtlas_initial_infinity_isPullback hπ data H m hj u hu b)

/-- Each actual union retains its original infinity inclusion. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedToGlobal_infinity (b : Bool) :
    pushout.inl i (l b) ≫ j b = c .infinity := pushout.inl_desc _ _ _

/-- Each actual union retains its original initial inclusion. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedToGlobal_initial (b : Bool) :
    pushout.inr i (l b) ≫ j b = c (.initial b) := pushout.inr_desc _ _ _

/-- The full node presentation has exactly the two original chart images. -/
theorem arithmeticZeroInfinityNormalizedToGlobal_range (b : Bool) :
    Set.range (j b) = Set.range (c .infinity) ∪ Set.range (c (.initial b)) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rcases SchemeOpenPushout.charts_cover i (l b) x with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact Or.inl ⟨a, (congrArg (fun k ↦ k a)
        (arithmeticZeroInfinityNormalizedToGlobal_infinity hπ data H m hj u hu b)).symm⟩
    · exact Or.inr ⟨a, (congrArg (fun k ↦ k a)
        (arithmeticZeroInfinityNormalizedToGlobal_initial hπ data H m hj u hu b)).symm⟩
  · rintro (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact ⟨pushout.inl i (l b) a, congrArg (fun k ↦ k a)
        (arithmeticZeroInfinityNormalizedToGlobal_infinity hπ data H m hj u hu b)⟩
    · exact ⟨pushout.inr i (l b) a, congrArg (fun k ↦ k a)
        (arithmeticZeroInfinityNormalizedToGlobal_initial hπ data H m hj u hu b)⟩

/-- Each complete source union is an actual open of the original corrected global stage. -/
def arithmeticZeroInfinityNormalizedUnion (b : Bool) : (X).Opens :=
  (c .infinity).opensRange ⊔ (c (.initial b)).opensRange

local notation "U" => arithmeticZeroInfinityNormalizedUnion hπ data H m hj u hu

/-- The full pair presentation identifies the actual original source open union. -/
def arithmeticZeroInfinityNormalizedUnionIso (b : Bool) :
    arithmeticZeroInfinityNormalizedPushout hπ data H m hj u hu b ≅ (U b).toScheme :=
  IsOpenImmersion.isoOfRangeEq (j b) (U b).ι (by
    rw [Scheme.Opens.range_ι, arithmeticZeroInfinityNormalizedToGlobal_range]
    rfl)

/-- The actual original union is a complete node, on both arms and at every order. -/
def arithmeticZeroInfinityNormalizedUnionNodeIso (b : Bool) :
    (U b).toScheme ≅ PolygonSmoothing.chart Q τ :=
  (arithmeticZeroInfinityNormalizedUnionIso hπ data H m hj u hu b).symm ≪≫ e b

/-- The union presentation retains its actual original global inclusion. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedUnionIso_global (b : Bool) :
    (arithmeticZeroInfinityNormalizedUnionIso hπ data H m hj u hu b).hom ≫ (U b).ι = j b :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end FLT.Mazur.WeierstrassDividedDepth
