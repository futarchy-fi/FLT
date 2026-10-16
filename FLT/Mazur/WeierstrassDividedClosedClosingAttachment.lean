/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedClosedTerminalNormalization
public import FLT.Mazur.WeierstrassDividedClosingAttachmentUnion

/-!
# The original closed closing pairs are untwisted full-node attachments

Each original pair is identified with its standard puncture pushout using
three constructed isomorphisms. Both pairs use the same full terminal
normalization. The original global-model pair unions are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 0
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 0
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "l" => leftBranchOpen Q (parameter R π 0)
local notation "r" => arithmeticOriginalClosingBoundary data H 0 j hj
local notation "L" => arithmeticClosingRetainedBoundary data H 0
local notation "C" => arithmeticRetainedFixedSmoothingIso data H 0 (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j))
local notation "P" => fixedTerminalPolygonIso π W (π ^ (1 + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale (j + 1)) H.a2_div
  (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu 0
local notation "N" => arithmeticClosedTerminalNormalization data H j hj u hu
local notation "v" => arithmeticRetainedClosingUnit data H 0 (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j))
local notation "B" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (LaurentUnitPoints.evalUnit (R := Q) v)))

/-- The target closing punctures have no residual twist at order zero. -/
def arithmeticClosedClosingPuncture (b : Bool) : branchTorus Q ⟶ PolygonSmoothing.chart Q τ :=
  if b then leftBranchOpen Q τ else rightBranchOpen Q τ

instance arithmeticClosedClosingPuncture_isOpenImmersion (b : Bool) :
    IsOpenImmersion (arithmeticClosedClosingPuncture data H b) := by
  cases b <;> dsimp [arithmeticClosedClosingPuncture] <;> infer_instance

local notation "p" => arithmeticClosedClosingPuncture data H

/-- The corrected whole terminal chart preserves the unchanged original source edge. -/
@[reassoc] theorem arithmeticClosedClosingSpan_terminal (b : Bool) :
    r b ≫ (P ≪≫ N).hom = B ≫ p b := by
  change r b ≫ (P).hom ≫ (N).hom = _
  have he : r b ≫ (P).hom =
      fixedTerminalPolygonBoundaryParameter data 0 j hj H.a1_unit (H.scale j)
        H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu b ≫ p b :=
    fixedTerminalPolygon_boundary ..
  rw [← Category.assoc, he, Category.assoc]
  exact arithmeticClosedTerminalNormalization_corrected data H j hj u hu b

/-- The standard full-node closing pushout, with the prescribed reciprocal retained puncture. -/
def arithmeticClosedUntwistedAttachment (b : Bool) : Scheme := pushout L (p b)

/-- The two full source charts and their original overlap give the untwisted span isomorphism. -/
def arithmeticClosedClosingSpanIso (b : Bool) :
    span l (r b) ≅ span L (p b) :=
  spanIsoMk (asIso B) C (P ≪≫ N) (arithmeticClosingSpan_retained data H 0 j hj)
    (arithmeticClosedClosingSpan_terminal data H j hj u hu b)

/-- Each original closing pair is isomorphic to its standard full-node attachment. -/
def arithmeticClosedClosingAttachmentIso (b : Bool) :
    arithmeticOriginalClosingAttachment data H 0 j hj b ≅
      arithmeticClosedUntwistedAttachment data H b :=
  asIso (pushout.map l (r b) L (p b) (C).hom (P ≪≫ N).hom B
    (arithmeticClosingSpan_retained data H 0 j hj)
    (arithmeticClosedClosingSpan_terminal data H j hj u hu b))

/-- The original full retained normalization is unchanged by the pair isomorphism. -/
@[reassoc] theorem arithmeticClosedClosingAttachmentIso_retained (b : Bool) :
    pushout.inl l (r b) ≫ (arithmeticClosedClosingAttachmentIso data H j hj u hu b).hom =
      (C).hom ≫ pushout.inl L (p b) := by
  simp [arithmeticClosedClosingAttachmentIso]

/-- Both pair isomorphisms use the same corrected full terminal chart. -/
@[reassoc] theorem arithmeticClosedClosingAttachmentIso_terminal (b : Bool) :
    pushout.inr l (r b) ≫ (arithmeticClosedClosingAttachmentIso data H j hj u hu b).hom =
      (P ≪≫ N).hom ≫ pushout.inr L (p b) := by
  simp [arithmeticClosedClosingAttachmentIso]

variable [IsDomain R] [IsBezout R] (hπ : π ≠ 0)
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction

/-- The untwisted attachment identifies the actual original two-label open union. -/
def arithmeticClosedClosingUnionIso (b : Bool) :
    (originalClosingChartUnion hπ data H 0 j hj b).toScheme ≅
      arithmeticClosedUntwistedAttachment data H b :=
  (originalClosingAttachmentUnionIso hπ data H 0 j hj b).symm ≪≫
    arithmeticClosedClosingAttachmentIso data H j hj u hu b

end FLT.Mazur.WeierstrassDividedDepth
