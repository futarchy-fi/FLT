/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedClosingMap
public import FLT.Mazur.WeierstrassDividedRevisedClosingIntersection
public import FLT.Mazur.SchemeOpenPushoutCoverIso

/-!
# Original closing unions identified inside the independent revised polygon

The full standard attachment embeds as exactly the two corresponding target
nodes. At first order the constructed original standardization therefore
identifies each entire original closing union with this actual target open.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (b : Bool)
local notation "Q" => Quotient R π m
local notation "σ" => arithmeticTerminalChangedSmoothing data H m j hj u hu
local notation "L" => arithmeticClosingRetainedBoundary data H m
local notation "P" => ite (b = true) (leftBranchOpen Q σ) (rightBranchOpen Q σ)
local notation "c" => Iso.hom (twistedRetainedOrientation data H m b) ≫
  arithmeticRevisedPolygonRetainedChart data H m j hj u hu (Fin.mk j (Nat.lt_succ_self j)) b
local notation "d" => arithmeticRevisedPolygonTerminalChart data H m j hj u hu
local notation "f" => arithmeticRevisedStandardClosingMap data H m j hj u hu b

instance arithmeticRevisedStandardClosingMap_isOpenImmersion : IsOpenImmersion f :=
  SchemeOpenPushout.coverDesc_isOpenImmersion L P c d
    (arithmeticRevisedPolygon_closing_isPullback data H m j hj u hu b)

/-- The standard attachment covers exactly its two whole node images in the revised polygon. -/
theorem arithmeticRevisedStandardClosingMap_range : Set.range f = Set.range c ∪ Set.range d := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rcases SchemeOpenPushout.charts_cover L P x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact Or.inl ⟨y, (congrArg (fun g ↦ g y)
        (arithmeticRevisedStandardClosingMap_retained data H m j hj u hu b)).symm⟩
    · exact Or.inr ⟨y, (congrArg (fun g ↦ g y)
        (arithmeticRevisedStandardClosingMap_terminal data H m j hj u hu b)).symm⟩
  · rintro (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact ⟨pushout.inl L P y, congrArg (fun g ↦ g y)
        (arithmeticRevisedStandardClosingMap_retained data H m j hj u hu b)⟩
    · exact ⟨pushout.inr L P y, congrArg (fun g ↦ g y)
        (arithmeticRevisedStandardClosingMap_terminal data H m j hj u hu b)⟩

/-- The actual open union of the corresponding two full target nodes. -/
def arithmeticRevisedClosingUnion : (arithmeticRevisedPolygon data H m j hj u hu).Opens :=
  (c).opensRange ⊔ (d).opensRange

/-- The full standard attachment is exactly the specified open in the independent target. -/
def arithmeticRevisedStandardClosingUnionIso :
    pushout L P ≅ (arithmeticRevisedClosingUnion data H m j hj u hu b).toScheme :=
  IsOpenImmersion.isoOfRangeEq f (arithmeticRevisedClosingUnion data H m j hj u hu b).ι
    (by rw [Scheme.Opens.range_ι, arithmeticRevisedStandardClosingMap_range]; rfl)

/-- The full union identification preserves its constructed target inclusion. -/
@[reassoc] theorem arithmeticRevisedStandardClosingUnionIso_target :
    (arithmeticRevisedStandardClosingUnionIso data H m j hj u hu b).hom ≫
      (arithmeticRevisedClosingUnion data H m j hj u hu b).ι = f :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

variable [IsDomain R] [IsBezout R] (hπ : π ≠ 0)
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction

/-- The original first-order closing open is identified with its actual revised target open. -/
def arithmeticFirstOriginalRevisedClosingUnionIso :
    (originalClosingChartUnion hπ data H 1 j hj b).toScheme ≅
      (arithmeticRevisedClosingUnion data H 1 j hj u hu b).toScheme :=
  arithmeticFirstOriginalStandardClosingUnionIso hπ data H j hj u hu b ≪≫
    arithmeticRevisedStandardClosingUnionIso data H 1 j hj u hu b

/-- This original-open identification is the previously constructed comparison into the target. -/
@[reassoc] theorem arithmeticFirstOriginalRevisedClosingUnionIso_target :
    (arithmeticFirstOriginalRevisedClosingUnionIso data H j hj u hu b hπ).hom ≫
      (arithmeticRevisedClosingUnion data H 1 j hj u hu b).ι =
        arithmeticFirstOriginalRevisedClosingUnionMap data H j hj u hu hπ b := by
  rw [arithmeticFirstOriginalRevisedClosingUnionIso, Iso.trans_hom, Category.assoc,
    arithmeticRevisedStandardClosingUnionIso_target]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
