/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalClosingIntersection

/-!
# Full original diagonal closing unions in the independent target

Each actual two-chart source union is its complete closing pushout, hence
isomorphic to the corresponding open union of the independent polygon.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFifthAtlasChart arithmeticZeroFiniteInitialIso arithmeticZeroFiniteLastIso
  arithmeticZeroFiniteTerminalIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticZeroDiagonalAtlasChart hπ data H m hj u hu
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu

local notation "s" => PolygonArithmeticSimultaneous.State.last D m
local notation "t" => PolygonArithmeticSimultaneous.State.terminal D m
local notation "E" => arithmeticZeroFiniteAtlasIso hπ data H m m hj u hu
local notation "G" => simultaneousTwistedArithmeticIso hπ data H m 0 hj u hu

variable (b : Bool)
local notation "l" => Iso.hom (edgeInversion Q) ≫ leftBranchOpen Q (s b)
local notation "r" => punctureOpen t b
local notation "c" => ι (ArithmeticChartLabel.retained (Fin.mk 0 (Nat.zero_lt_succ 0)) b)
local notation "d" => ι ArithmeticChartLabel.terminal

/-- The complete diagonal attachment maps to the original simultaneous stage. -/
def arithmeticZeroDiagonalClosingToGlobal :
    pushout l r ⟶ simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu :=
  pushout.desc c d (arithmeticZeroDiagonalAtlas_closing_isPullback hπ data H m hj u hu b).w

local notation "g" => arithmeticZeroDiagonalClosingToGlobal hπ data H m hj u hu b

instance arithmeticZeroDiagonalClosingToGlobal_isOpenImmersion : IsOpenImmersion g :=
  SchemeOpenPushout.coverDesc_isOpenImmersion l r c d
    (arithmeticZeroDiagonalAtlas_closing_isPullback hπ data H m hj u hu b)

/-- The actual attachment preserves its full retained chart. -/
@[reassoc] theorem arithmeticZeroDiagonalClosingToGlobal_retained :
    pushout.inl l r ≫ g = c := pushout.inl_desc _ _ _

/-- Both actual attachments preserve their common full terminal chart. -/
@[reassoc] theorem arithmeticZeroDiagonalClosingToGlobal_terminal :
    pushout.inr l r ≫ g = d := pushout.inr_desc _ _ _

/-- The attachment covers precisely the two actual source chart images. -/
theorem arithmeticZeroDiagonalClosingToGlobal_range :
    Set.range g = Set.range c ∪ Set.range d := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rcases SchemeOpenPushout.charts_cover l r x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact Or.inl ⟨y, (congrArg (fun a ↦ a y)
        (arithmeticZeroDiagonalClosingToGlobal_retained hπ data H m hj u hu b)).symm⟩
    · exact Or.inr ⟨y, (congrArg (fun a ↦ a y)
        (arithmeticZeroDiagonalClosingToGlobal_terminal hπ data H m hj u hu b)).symm⟩
  · rintro (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact ⟨pushout.inl l r y, congrArg (fun a ↦ a y)
        (arithmeticZeroDiagonalClosingToGlobal_retained hπ data H m hj u hu b)⟩
    · exact ⟨pushout.inr l r y, congrArg (fun a ↦ a y)
        (arithmeticZeroDiagonalClosingToGlobal_terminal hπ data H m hj u hu b)⟩

/-- The actual closing union contains the full source retained and terminal charts. -/
def arithmeticZeroDiagonalClosingUnion :
    (simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu).Opens :=
  (c).opensRange ⊔ (d).opensRange

/-- The actual diagonal closing union is its full normalized pushout. -/
def arithmeticZeroDiagonalClosingUnionIso :
    pushout l r ≅ (arithmeticZeroDiagonalClosingUnion hπ data H m hj u hu b).toScheme :=
  IsOpenImmersion.isoOfRangeEq g (arithmeticZeroDiagonalClosingUnion hπ data H m hj u hu b).ι
    (by rw [Scheme.Opens.range_ι, arithmeticZeroDiagonalClosingToGlobal_range]; rfl)

/-- The source-union identification preserves the original full global embedding. -/
@[reassoc] theorem arithmeticZeroDiagonalClosingUnionIso_global :
    (arithmeticZeroDiagonalClosingUnionIso hπ data H m hj u hu b).hom ≫
      (arithmeticZeroDiagonalClosingUnion hπ data H m hj u hu b).ι = g :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- Each complete actual diagonal closing union identifies its independent target open. -/
def arithmeticZeroDiagonalClosingComparisonIso :
    (arithmeticZeroDiagonalClosingUnion hπ data H m hj u hu b).toScheme ≅
      (arithmeticZeroDiagonalPolygonClosingUnion hπ data H m hj u hu b).toScheme :=
  (arithmeticZeroDiagonalClosingUnionIso hπ data H m hj u hu b).symm ≪≫
    arithmeticZeroDiagonalPolygonClosingUnionIso hπ data H m hj u hu b

/-- The whole source-union comparison is the previously constructed full target attachment. -/
@[reassoc] theorem arithmeticZeroDiagonalClosingComparisonIso_target :
    (arithmeticZeroDiagonalClosingUnionIso hπ data H m hj u hu b).hom ≫
      (arithmeticZeroDiagonalClosingComparisonIso hπ data H m hj u hu b).hom ≫
        (arithmeticZeroDiagonalPolygonClosingUnion hπ data H m hj u hu b).ι =
          arithmeticZeroDiagonalClosingMap hπ data H m hj u hu b := by
  rw [arithmeticZeroDiagonalClosingComparisonIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc, arithmeticZeroDiagonalPolygonClosingUnionIso_target]

end FLT.Mazur.WeierstrassDividedDepth
