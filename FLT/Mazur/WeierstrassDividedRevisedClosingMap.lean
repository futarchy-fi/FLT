/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedPolygonEdges
public import FLT.Mazur.WeierstrassDividedTerminalFirstResidualGluing

/-!
# Original first-order closing attachments in the revised cyclic target

Both complete original closing pairs map into the independently constructed
polygon. Their maps use the already constructed first-order standardization,
with one common corrected terminal and both original retained orientations.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "σ" => arithmeticTerminalChangedSmoothing data H m j hj u hu
local notation "L" => arithmeticClosingRetainedBoundary data H m
local notation "P" => fun (b : Bool) ↦
  ite (b = true) (leftBranchOpen Q σ) (rightBranchOpen Q σ)
local notation "O" => twistedRetainedOrientation data H m
local notation "c" => arithmeticRevisedPolygonRetainedChart data H m j hj u hu
local notation "d" => arithmeticRevisedPolygonTerminalChart data H m j hj u hu

instance arithmeticRevisedClosingBoundary_isOpenImmersion (b : Bool) :
    IsOpenImmersion (P b) := by
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

/-- The whole standard two-node attachment maps to the independent revised target. -/
def arithmeticRevisedStandardClosingMap (b : Bool) :
    pushout L (P b) ⟶ arithmeticRevisedPolygon data H m j hj u hu :=
  pushout.desc ((O b).hom ≫ c ⟨j, by omega⟩ b) d
    (arithmeticRevisedPolygon_closing data H m j hj u hu b)

/-- Its retained restriction is the full original orientation followed by its cyclic label. -/
@[reassoc] theorem arithmeticRevisedStandardClosingMap_retained (b : Bool) :
    pushout.inl L (P b) ≫ arithmeticRevisedStandardClosingMap data H m j hj u hu b =
      (O b).hom ≫ c ⟨j, by omega⟩ b := pushout.inl_desc _ _ _

/-- Both branches use exactly the same entire terminal chart in the revised target. -/
@[reassoc] theorem arithmeticRevisedStandardClosingMap_terminal (b : Bool) :
    pushout.inr L (P b) ≫ arithmeticRevisedStandardClosingMap data H m j hj u hu b = d :=
  pushout.inr_desc _ _ _

variable [IsDomain R] (hπ : π ≠ 0)

/-- The actual original first-order pair maps through its constructed standardization. -/
def arithmeticFirstOriginalRevisedClosingMap (b : Bool) :
    arithmeticOriginalClosingAttachment data H 1 j hj b ⟶
      arithmeticRevisedPolygon data H 1 j hj u hu :=
  (arithmeticFirstOriginalStandardClosingIso hπ data H j hj u hu b).hom ≫
    arithmeticRevisedStandardClosingMap data H 1 j hj u hu b

variable [IsBezout R]
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction

/-- Each complete original closing union maps into the revised first-order target. -/
def arithmeticFirstOriginalRevisedClosingUnionMap (b : Bool) :
    (originalClosingChartUnion hπ data H 1 j hj b).toScheme ⟶
      arithmeticRevisedPolygon data H 1 j hj u hu :=
  (arithmeticFirstOriginalStandardClosingUnionIso hπ data H j hj u hu b).hom ≫
    arithmeticRevisedStandardClosingMap data H 1 j hj u hu b

end FLT.Mazur.WeierstrassDividedDepth
