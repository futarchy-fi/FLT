/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedClosingTransportRestriction

/-!
# Restriction of the original and twisted closing attachments

The two pushouts inherit the actual chart restriction maps. The constructed
comparison isomorphism and its inverse commute with these arrows, for either
terminal branch independently.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
local notation "l" => fun a ↦ leftBranchOpen (Quotient R π a) (parameter R π a)
local notation "r" => fun a b ↦ arithmeticOriginalClosingBoundary data H a j hj b
local notation "L" => fun a ↦ arithmeticClosingRetainedBoundary data H a
local notation "ρ" => closingOverlapRestriction (R := R) (π := π) m
local notation "S" => closingRetainedRestriction (R := R) (π := π) m
local notation "N" => closingNormalizedRestriction data H m
local notation "D" => closingTerminalRestriction data H m j hj

/-- Restriction of the original attachment is induced by the unchanged source chart maps. -/
def originalClosingAttachmentRestriction (b : Bool) :
    arithmeticOriginalClosingAttachment data H m j hj b ⟶
      arithmeticOriginalClosingAttachment data H (m + 1) j hj b :=
  pushout.map (l m) (r m b) (l (m + 1)) (r (m + 1) b) S D ρ
    (closingOriginalRetained_restriction m)
    (closingOriginalTerminal_restriction data H m j hj b)

/-- On the retained chart the original attachment restriction is the original coefficient map. -/
@[reassoc] theorem originalClosingAttachmentRestriction_retained (b : Bool) :
    pushout.inl (l m) (r m b) ≫ originalClosingAttachmentRestriction data H m j hj b =
      S ≫ pushout.inl (l (m + 1)) (r (m + 1) b) := by
  simp [originalClosingAttachmentRestriction]

/-- On the terminal chart it retains the complete original smoothing. -/
@[reassoc] theorem originalClosingAttachmentRestriction_terminal (b : Bool) :
    pushout.inr (l m) (r m b) ≫ originalClosingAttachmentRestriction data H m j hj b =
      D ≫ pushout.inr (l (m + 1)) (r (m + 1) b) := by
  simp [originalClosingAttachmentRestriction]

variable [IsDomain R] (hπ : π ≠ 0)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "M" => fun a b ↦ arithmeticClosingTerminalBoundary data H a j hj u hu b
local notation "I" => fun a b ↦ arithmeticClosingAttachmentIso data H a j hj u hu b
local notation "C" => fun a ↦ arithmeticRetainedFixedSmoothingIso data H a (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j))
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "P" => fun a ↦ fixedTerminalPolygonIso π W (π ^ (1 + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale (j + 1)) H.a2_div
  (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu a

/-- The normalized attachment restricts along the exact transported boundary squares. -/
def twistedClosingAttachmentRestriction (b : Bool) :
    arithmeticTwistedClosingAttachment data H m j hj u hu b ⟶
      arithmeticTwistedClosingAttachment data H (m + 1) j hj u hu b :=
  pushout.map (L m) (M m b) (L (m + 1)) (M (m + 1) b) N N ρ
    (closingTransportRetained_restriction data H m j hj)
    (closingTransportTerminal_restriction data H m j hj hπ u hu b)

/-- The transported retained chart restricts by the fixed smoothing coefficient map. -/
@[reassoc] theorem twistedClosingAttachmentRestriction_retained (b : Bool) :
    pushout.inl (L m) (M m b) ≫
      twistedClosingAttachmentRestriction data H m j hj hπ u hu b =
        N ≫ pushout.inl (L (m + 1)) (M (m + 1) b) := by
  exact pushout.inl_desc _ _ _

/-- The transported terminal chart uses the same full normalized coefficient map. -/
@[reassoc] theorem twistedClosingAttachmentRestriction_terminal (b : Bool) :
    pushout.inr (L m) (M m b) ≫
      twistedClosingAttachmentRestriction data H m j hj hπ u hu b =
        N ≫ pushout.inr (L (m + 1)) (M (m + 1) b) := by
  exact pushout.inr_desc _ _ _

/-- The full two-chart comparison commutes with the actual pushout restriction maps. -/
@[reassoc] theorem closingAttachmentIso_restriction (b : Bool) :
    originalClosingAttachmentRestriction data H m j hj b ≫ (I (m + 1) b).hom =
      (I m b).hom ≫ twistedClosingAttachmentRestriction data H m j hj hπ u hu b := by
  have hc : S ≫ (C (m + 1)).hom = (C m).hom ≫ N :=
    arithmeticRetainedFixedSmoothingIso_restriction data H m (j + 1) hj ⟨j, by omega⟩
  have hp : D ≫ (P (m + 1)).hom = (P m).hom ≫ N :=
    fixedTerminalPolygonIso_restriction π W (π ^ (1 + j + 1))
      (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale (j + 1)) H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu hπ m
  apply pushout.hom_ext
  · simp only [originalClosingAttachmentRestriction_retained_assoc,
      arithmeticClosingAttachmentIso_retained, arithmeticClosingAttachmentIso_retained_assoc,
      twistedClosingAttachmentRestriction_retained]
    rw [← Category.assoc, hc, Category.assoc]
  · simp only [originalClosingAttachmentRestriction_terminal_assoc,
      arithmeticClosingAttachmentIso_terminal, arithmeticClosingAttachmentIso_terminal_assoc,
      twistedClosingAttachmentRestriction_terminal]
    rw [← Category.assoc, hp, Category.assoc]

/-- The full inverse gluing comparison preserves the same arithmetic arrows. -/
@[reassoc] theorem closingAttachmentIso_inv_restriction (b : Bool) :
    twistedClosingAttachmentRestriction data H m j hj hπ u hu b ≫ (I (m + 1) b).inv =
      (I m b).inv ≫ originalClosingAttachmentRestriction data H m j hj b := by
  apply (cancel_mono (I (m + 1) b).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    closingAttachmentIso_restriction data H m j hj hπ,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end FLT.Mazur.WeierstrassDividedDepth
