/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalPolygonIntersection
public import FLT.Mazur.SchemeOpenPushoutCoverIso

/-!
# The actual diagonal closing open unions in the independent target

The two retained nodes and the common terminal retain their distinct actual
smoothings. Their entire Laurent attachments satisfy the original orientations.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "p" => arithmeticZeroDiagonalPolygonParameter hπ data H hj u hu m
local notation "s" => PolygonArithmeticSimultaneous.State.last D m
local notation "t" => PolygonArithmeticSimultaneous.State.terminal D m
local notation "c" => arithmeticZeroDiagonalPolygonRetainedChart hπ data H m hj u hu
local notation "d" => arithmeticZeroDiagonalPolygonTerminalChart hπ data H m hj u hu

local notation "f" => arithmeticZeroDiagonalPolygonRetainedMap hπ data H m hj u hu

variable (b : Bool)
local notation "l" => Iso.hom (edgeInversion Q) ≫ leftBranchOpen Q (s b)
local notation "r" => punctureOpen t b
local notation "g" => arithmeticZeroDiagonalClosingMap hπ data H m hj u hu b

instance arithmeticZeroDiagonalPolygonTerminalChart_isOpenImmersion : IsOpenImmersion d := by
  unfold arithmeticZeroDiagonalPolygonTerminalChart
  infer_instance

instance arithmeticZeroDiagonalPolygonRetainedMap_isOpenImmersion (b : Bool) :
    IsOpenImmersion (f b) := by
  unfold arithmeticZeroDiagonalPolygonRetainedMap
  split <;> infer_instance

instance arithmeticZeroDiagonalClosingMap_isOpenImmersion : IsOpenImmersion g :=
  SchemeOpenPushout.coverDesc_isOpenImmersion l r (f b) d
    (arithmeticZeroDiagonalPolygon_closing_isPullback hπ data H m hj u hu b)

/-- The complete attachment has exactly the two full target node images. -/
theorem arithmeticZeroDiagonalClosingMap_range :
    Set.range g = Set.range (f b) ∪ Set.range d := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rcases SchemeOpenPushout.charts_cover l r x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact Or.inl ⟨y, (congrArg (fun a ↦ a y)
        (arithmeticZeroDiagonalClosingMap_retained hπ data H m hj u hu b)).symm⟩
    · exact Or.inr ⟨y, (congrArg (fun a ↦ a y)
        (arithmeticZeroDiagonalClosingMap_terminal hπ data H m hj u hu b)).symm⟩
  · rintro (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact ⟨pushout.inl l r y, congrArg (fun a ↦ a y)
        (arithmeticZeroDiagonalClosingMap_retained hπ data H m hj u hu b)⟩
    · exact ⟨pushout.inr l r y, congrArg (fun a ↦ a y)
        (arithmeticZeroDiagonalClosingMap_terminal hπ data H m hj u hu b)⟩

/-- The specified closing union includes both complete diagonal nodes. -/
def arithmeticZeroDiagonalPolygonClosingUnion :
    (arithmeticZeroDiagonalPolygon hπ data H m hj u hu).Opens :=
  (f b).opensRange ⊔ (d).opensRange

/-- The full closing pushout is the actual open union of its two diagonal nodes. -/
def arithmeticZeroDiagonalPolygonClosingUnionIso :
    pushout l r ≅ (arithmeticZeroDiagonalPolygonClosingUnion hπ data H m hj u hu b).toScheme :=
  IsOpenImmersion.isoOfRangeEq g
    (arithmeticZeroDiagonalPolygonClosingUnion hπ data H m hj u hu b).ι
    (by rw [Scheme.Opens.range_ι, arithmeticZeroDiagonalClosingMap_range]; rfl)

/-- The union identification preserves the constructed comparison into the whole target. -/
@[reassoc] theorem arithmeticZeroDiagonalPolygonClosingUnionIso_target :
    (arithmeticZeroDiagonalPolygonClosingUnionIso hπ data H m hj u hu b).hom ≫
      (arithmeticZeroDiagonalPolygonClosingUnion hπ data H m hj u hu b).ι = g :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end FLT.Mazur.WeierstrassDividedDepth
