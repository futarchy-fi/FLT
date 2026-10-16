/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedClosedClosingAttachment
public import FLT.Mazur.WeierstrassDividedClosedPolygonDescent
public import FLT.Mazur.PolygonSmoothingClosingPair

/-!
# Original closed closing pairs identify actual polygon open unions

Both original two-label open unions are identified with their prescribed
polygon unions. The isomorphisms recover the already descended global map;
there is no replacement of the original overlaps or terminal comparison.
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
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 0
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 0
local notation "hn" => Fact.mk
  (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ 1) π 0 H.scale_div)
local notation "Y" => arithmeticFactorRatioPolygon π 0 W (π ^ 1)
  H.a1_unit H.scale_div (j + 1)
local notation "l" => leftBranchOpen Q (parameter R π 0)
local notation "r" => arithmeticOriginalClosingBoundary data H 0 j hj
local notation "L" => arithmeticClosingRetainedBoundary data H 0
local notation "p" => arithmeticClosedClosingPuncture data H
local notation "F" => arithmeticClosedPolygonMap hπ data H j hj u hu
local notation "I" => arithmeticClosedClosingAttachmentIso data H j hj u hu
local notation "f" => @retainedPolygonMap Q _ τ hn (j + 1) (Fin.mk j (Nat.lt_succ_self j))
local notation "c" => @PolygonInfinitesimal.chart Q _ τ hn (2 * (j + 1) + 3) (by omega)

/-- The exact target open union retains the original last label on each arm and label zero. -/
def arithmeticClosedClosingPolygonUnion (b : Bool) : (Y).Opens :=
  (f b).opensRange ⊔ (c 0).opensRange

/-- The normalized closing attachment has its explicit actual polygon embedding. -/
def arithmeticClosedClosingToPolygon (b : Bool) :
    arithmeticClosedUntwistedAttachment data H b ⟶ Y := by
  let _ := hn
  exact closingPairToPolygon Q τ j b

instance arithmeticClosedClosingToPolygon_isOpenImmersion (b : Bool) :
    IsOpenImmersion (arithmeticClosedClosingToPolygon data H j b) := by
  let _ := hn
  exact closingPairToPolygon_isOpenImmersion Q τ j b

/-- The full normalized closing attachment is the specified polygon open union. -/
def arithmeticClosedClosingTargetIso (b : Bool) :
    arithmeticClosedUntwistedAttachment data H b ≅
      (arithmeticClosedClosingPolygonUnion data H j b).toScheme := by
  let _ := hn
  exact closingPairUnionIso Q τ j b

/-- The original closing attachment comparison is the global map on the whole pair. -/
@[reassoc] theorem arithmeticClosedClosingToPolygon_original (b : Bool) :
    (I b).hom ≫ arithmeticClosedClosingToPolygon data H j b =
      originalClosingAttachmentToGlobal hπ data H 0 j hj b ≫ F := by
  let _ := hn
  apply pushout.hom_ext
  · rw [arithmeticClosedClosingAttachmentIso_retained_assoc,
      originalClosingAttachmentToGlobal_retained_assoc, arithmeticClosedPolygonMap_chart]
    change _ ≫ (pushout.inl ((edgeInversion Q).hom ≫ leftBranchOpen Q τ)
      (closingPairPuncture Q τ b) ≫ closingPairToPolygon Q τ j b) = _
    rw [closingPairToPolygon_retained]
    cases b <;> rfl
  · rw [arithmeticClosedClosingAttachmentIso_terminal_assoc,
      originalClosingAttachmentToGlobal_terminal_assoc, arithmeticClosedPolygonMap_chart]
    change _ ≫ (pushout.inr ((edgeInversion Q).hom ≫ leftBranchOpen Q τ)
      (closingPairPuncture Q τ b) ≫ closingPairToPolygon Q τ j b) = _
    rw [closingPairToPolygon_terminal, Iso.trans_hom, Category.assoc]
    rfl

/-- Each actual original two-label union is isomorphic to the corresponding polygon union. -/
def arithmeticClosedClosingPolygonUnionIso (b : Bool) :
    (originalClosingChartUnion hπ data H 0 j hj b).toScheme ≅
      (arithmeticClosedClosingPolygonUnion data H j b).toScheme :=
  arithmeticClosedClosingUnionIso data H j hj u hu hπ b ≪≫
    arithmeticClosedClosingTargetIso data H j b

/-- The isomorphism on the entire original pair recovers the descended comparison. -/
@[reassoc] theorem arithmeticClosedClosingPolygonUnionIso_global (b : Bool) :
    (arithmeticClosedClosingPolygonUnionIso hπ data H j hj u hu b).hom ≫
      (arithmeticClosedClosingPolygonUnion data H j b).ι =
        (originalClosingChartUnion hπ data H 0 j hj b).ι ≫ F := by
  let _ := hn
  apply (cancel_epi (originalClosingAttachmentUnionIso hπ data H 0 j hj b).hom).mp
  dsimp only [arithmeticClosedClosingPolygonUnionIso, arithmeticClosedClosingUnionIso,
    Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have ht : (arithmeticClosedClosingTargetIso data H j b).hom ≫
      (arithmeticClosedClosingPolygonUnion data H j b).ι =
        arithmeticClosedClosingToPolygon data H j b :=
    closingPairUnionIso_polygon Q τ j b
  rw [ht]
  rw [arithmeticClosedClosingToPolygon_original,
    originalClosingAttachmentUnionIso_global_assoc]

/-- The global comparison is an open immersion on each full original closing union. -/
instance arithmeticClosedPolygonMap_closing_isOpenImmersion (b : Bool) :
    IsOpenImmersion ((originalClosingChartUnion hπ data H 0 j hj b).ι ≫ F) := by
  rw [← arithmeticClosedClosingPolygonUnionIso_global hπ data H j hj u hu b]
  infer_instance

end FLT.Mazur.WeierstrassDividedDepth
