/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedClosingTransportGluing
public import FLT.Mazur.WeierstrassDividedArithmeticLabeledTerminalEdge
public import FLT.Mazur.SchemeOpenPushoutCoverIso

/-!
# Each original closing attachment is its actual global-model open union

The unchanged Laurent edge is the full intersection of the terminal chart and
last retained chart. Their pushout therefore embeds into the original global
arithmetic stage, with image exactly the union of those two labeled charts.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n) (b : Bool)
local notation "Q" => Quotient R π m
local notation "l" => leftBranchOpen Q (parameter R π m)
local notation "r" => arithmeticOriginalClosingBoundary data H m j hj b
local notation "c" => arithmeticLabeledAtlasMap hπ data H m (j + 1) hj
local notation "a" => ArithmeticChartLabel.retained (Fin.mk j (Nat.lt_succ_self j)) b

/-- The original closing span is the full intersection of the actual labeled chart maps. -/
theorem originalClosingAttachment_isPullback : IsPullback l r (c a) (c .terminal) := by
  have ht : IsPullback r l (c .terminal) (c a) := by
    dsimp only [arithmeticOriginalClosingBoundary, arithmeticLabeledAtlasMap,
      arithmeticLabeledTerminalChart, arithmeticLabeledRetainedChart]
    rw [arithmeticRetainedTensorChart_newest]
    exact terminalArithmeticNodeEvaluation_isPullback data m j hj H.a1_unit (H.scale j)
      H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) b hπ
  exact ht.flip

attribute [local irreducible] arithmeticOriginalClosingBoundary arithmeticLabeledAtlasMap

/-- The pair gluing maps to the original global stage by its original labeled inclusions. -/
def originalClosingAttachmentToGlobal :
    arithmeticOriginalClosingAttachment data H m j hj b ⟶
      finiteGlobalArithmeticStage hπ data (j + 1) hj m :=
  pushout.desc (c a) (c .terminal)
    (originalClosingAttachment_isPullback hπ data H m j hj b).w

/-- This gluing is an actual open submodel, with no extra identifications. -/
instance originalClosingAttachmentToGlobal_isOpenImmersion :
    IsOpenImmersion (originalClosingAttachmentToGlobal hπ data H m j hj b) :=
  SchemeOpenPushout.coverDesc_isOpenImmersion l r (c a) (c .terminal)
    (originalClosingAttachment_isPullback hπ data H m j hj b)

/-- The original retained chart is preserved by the actual global embedding. -/
@[reassoc] theorem originalClosingAttachmentToGlobal_retained :
    pushout.inl l r ≫ originalClosingAttachmentToGlobal hπ data H m j hj b = c a :=
  pushout.inl_desc _ _ _

/-- The original full terminal chart is preserved by the actual global embedding. -/
@[reassoc] theorem originalClosingAttachmentToGlobal_terminal :
    pushout.inr l r ≫ originalClosingAttachmentToGlobal hπ data H m j hj b = c .terminal :=
  pushout.inr_desc _ _ _

/-- The image is precisely the union of the two actual original labeled charts. -/
theorem originalClosingAttachmentToGlobal_range :
    Set.range (originalClosingAttachmentToGlobal hπ data H m j hj b) =
      Set.range (c a) ∪ Set.range (c .terminal) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rcases SchemeOpenPushout.charts_cover l r x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · left
      exact ⟨y, (congrArg (fun f ↦ f y)
        (originalClosingAttachmentToGlobal_retained hπ data H m j hj b)).symm⟩
    · right
      exact ⟨y, (congrArg (fun f ↦ f y)
        (originalClosingAttachmentToGlobal_terminal hπ data H m j hj b)).symm⟩
  · rintro (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact ⟨pushout.inl l r y, congrArg (fun f ↦ f y)
        (originalClosingAttachmentToGlobal_retained hπ data H m j hj b)⟩
    · exact ⟨pushout.inr l r y, congrArg (fun f ↦ f y)
        (originalClosingAttachmentToGlobal_terminal hπ data H m j hj b)⟩

/-- The actual two-label open union inside the original global arithmetic stage. -/
def originalClosingChartUnion :
    (finiteGlobalArithmeticStage hπ data (j + 1) hj m).Opens :=
  (c a).opensRange ⊔ (c .terminal).opensRange

/-- The original pair attachment is isomorphic to the specified actual global-model union. -/
def originalClosingAttachmentUnionIso :
    arithmeticOriginalClosingAttachment data H m j hj b ≅
      (originalClosingChartUnion hπ data H m j hj b).toScheme :=
  IsOpenImmersion.isoOfRangeEq (originalClosingAttachmentToGlobal hπ data H m j hj b)
    (originalClosingChartUnion hπ data H m j hj b).ι (by
      rw [Scheme.Opens.range_ι, originalClosingAttachmentToGlobal_range]
      rfl)

/-- The union identification retains the original map to the whole global stage. -/
@[reassoc] theorem originalClosingAttachmentUnionIso_global :
    (originalClosingAttachmentUnionIso hπ data H m j hj b).hom ≫
      (originalClosingChartUnion hπ data H m j hj b).ι =
        originalClosingAttachmentToGlobal hπ data H m j hj b :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

variable (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)

/-- Each transported target attachment is identified with its actual original global union. -/
def twistedClosingAttachmentUnionIso :
    arithmeticTwistedClosingAttachment data H m j hj u hu b ≅
      (originalClosingChartUnion hπ data H m j hj b).toScheme :=
  (arithmeticClosingAttachmentIso data H m j hj u hu b).symm ≪≫
    originalClosingAttachmentUnionIso hπ data H m j hj b

/-- Transport and global-union identification recover exactly the original open embedding. -/
@[reassoc] theorem twistedClosingAttachmentUnionIso_global :
    (arithmeticClosingAttachmentIso data H m j hj u hu b).hom ≫
      (twistedClosingAttachmentUnionIso hπ data H m j hj b u hu).hom ≫
        (originalClosingChartUnion hπ data H m j hj b).ι =
          originalClosingAttachmentToGlobal hπ data H m j hj b := by
  simp only [twistedClosingAttachmentUnionIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc, originalClosingAttachmentUnionIso_global]

end FLT.Mazur.WeierstrassDividedDepth
