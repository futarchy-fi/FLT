/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalChangedSmoothing
public import FLT.Mazur.WeierstrassDividedClosingAttachmentUnion

/-!
# Closing attachments with the changed terminal smoothing

Both original whole-chart spans identify pushouts with the changed terminal
chart and its exact residual gluing. The original retained chart and source
punctures are unchanged, and no vanishing residual twist is assumed.
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
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "l" => leftBranchOpen Q (parameter R π m)
local notation "r" => arithmeticOriginalClosingBoundary data H m j hj
local notation "L" => arithmeticClosingRetainedBoundary data H m
local notation "C" => arithmeticRetainedFixedSmoothingIso data H m (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j))
local notation "P" => fixedTerminalPolygonIso π W (π ^ (1 + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale (j + 1)) H.a2_div
  (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu m
local notation "N" => arithmeticTerminalChangedIso data H m j hj u hu
local notation "v" => arithmeticRetainedClosingUnit data H m (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j))
local notation "B" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (LaurentUnitPoints.evalUnit (R := Q) v)))

local notation "p" => arithmeticTerminalChangedBoundary data H m j hj u hu

/-- The corrected whole terminal chart preserves the unchanged original source edge. -/
@[reassoc] theorem arithmeticChangedClosingSpan_terminal (b : Bool) :
    r b ≫ (P ≪≫ N).hom = B ≫ p b := by
  change r b ≫ (P).hom ≫ (N).hom = _
  rw [← Category.assoc]
  have he : r b ≫ (P).hom =
      B ≫ arithmeticClosingTerminalBoundary data H m j hj u hu b :=
    arithmeticClosingSpan_terminal data H m j hj u hu b
  rw [he, Category.assoc, arithmeticTerminalChangedBoundary_transport]

/-- The full-node closing pushout with the changed terminal smoothing and residual transition. -/
def arithmeticChangedClosingAttachment (b : Bool) : Scheme := pushout L (p b)

/-- The two full source charts and their original overlap give the revised span isomorphism. -/
def arithmeticChangedClosingSpanIso (b : Bool) :
    span l (r b) ≅ span L (p b) :=
  spanIsoMk (asIso B) C (P ≪≫ N) (arithmeticClosingSpan_retained data H m j hj)
    (arithmeticChangedClosingSpan_terminal data H m j hj u hu b)

/-- Each original closing pair is isomorphic to its revised full-node attachment. -/
def arithmeticChangedClosingAttachmentIso (b : Bool) :
    arithmeticOriginalClosingAttachment data H m j hj b ≅
      arithmeticChangedClosingAttachment data H m j hj u hu b :=
  asIso (pushout.map l (r b) L (p b) (C).hom (P ≪≫ N).hom B
    (arithmeticClosingSpan_retained data H m j hj)
    (arithmeticChangedClosingSpan_terminal data H m j hj u hu b))

/-- The original full retained normalization is unchanged by the pair isomorphism. -/
@[reassoc] theorem arithmeticChangedClosingAttachmentIso_retained (b : Bool) :
    pushout.inl l (r b) ≫ (arithmeticChangedClosingAttachmentIso data H m j hj u hu b).hom =
      (C).hom ≫ pushout.inl L (p b) := by
  simp [arithmeticChangedClosingAttachmentIso]

/-- Both pair isomorphisms use the same corrected full terminal chart. -/
@[reassoc] theorem arithmeticChangedClosingAttachmentIso_terminal (b : Bool) :
    pushout.inr l (r b) ≫ (arithmeticChangedClosingAttachmentIso data H m j hj u hu b).hom =
      (P ≪≫ N).hom ≫ pushout.inr L (p b) := by
  simp [arithmeticChangedClosingAttachmentIso]

variable [IsDomain R] [IsBezout R] (hπ : π ≠ 0)
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction

/-- The revised attachment identifies the actual original two-label open union. -/
def arithmeticChangedClosingUnionIso (b : Bool) :
    (originalClosingChartUnion hπ data H m j hj b).toScheme ≅
      arithmeticChangedClosingAttachment data H m j hj u hu b :=
  (originalClosingAttachmentUnionIso hπ data H m j hj b).symm ≪≫
    arithmeticChangedClosingAttachmentIso data H m j hj u hu b

end FLT.Mazur.WeierstrassDividedDepth
