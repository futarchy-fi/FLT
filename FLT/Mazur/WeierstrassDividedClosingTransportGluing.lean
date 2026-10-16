/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedClosingTransportSpan
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalNodeOpen
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Glue the transported original closing pair

For each terminal branch, the two complete original charts glued on their
original edge are isomorphic to the constructed twisted attachment. This is
one closing pair, not an identification of the full global polygon quotient.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "v" => arithmeticRetainedClosingUnit data H m (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j))
local notation "B" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (LaurentUnitPoints.evalUnit (R := Q) v)))
local notation "T" => fixedTerminalPolygonBoundaryParameter data m j hj
  H.a1_unit (H.scale j) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu
local notation "E" => terminalArithmeticNodeEvaluation data m j hj
  H.a1_unit (H.scale j) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "P" => fixedTerminalPolygonIso π W (π ^ (1 + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale (j + 1)) H.a2_div
  (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu m

local notation "C" => arithmeticRetainedFixedSmoothingIso data H m (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j))

local notation "l" => leftBranchOpen Q (parameter R π m)
local notation "c" => arithmeticTerminalSmoothing π m W (π ^ (1 + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale (j + 1)) H.a2_div
  (H.b4_div _) (H.b6_div _)

/-- The original terminal node attachment, named to retain its arithmetic data in instances. -/
def arithmeticOriginalClosingBoundary (b : Bool) :
    branchTorus Q ⟶ Spec (.of (NodalFiber.Coordinate c)) :=
  Spec.map (CommRingCat.ofHom (E b).toRingHom)

local notation "r" => arithmeticOriginalClosingBoundary data H m j hj
local notation "L" => arithmeticClosingRetainedBoundary data H m
local notation "M" => arithmeticClosingTerminalBoundary data H m j hj u hu

instance arithmeticOriginalClosingBoundary_isOpenImmersion (b : Bool) :
    IsOpenImmersion (r b) :=
  terminalArithmeticNodeEvaluation_isOpenImmersion data m j hj H.a1_unit (H.scale j)
    H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) b

attribute [local irreducible] arithmeticOriginalClosingBoundary

/-- Glue the two original whole charts along the unchanged source closing edge. -/
def arithmeticOriginalClosingAttachment (b : Bool) : Scheme := pushout l (r b)

/-- Glue the normalized whole charts with the constructed full terminal twist. -/
def arithmeticTwistedClosingAttachment (b : Bool) : Scheme := pushout L (M b)

/-- The full closing-pair gluing comparison is constructed from the three actual isomorphisms. -/
def arithmeticClosingAttachmentIso (b : Bool) :
    arithmeticOriginalClosingAttachment data H m j hj b ≅
      arithmeticTwistedClosingAttachment data H m j hj u hu b :=
  asIso (pushout.map l (r b) L (M b) (C).hom (P).hom B
    (arithmeticClosingSpan_retained data H m j hj)
    (by simpa only [arithmeticOriginalClosingBoundary] using
      arithmeticClosingSpan_terminal data H m j hj u hu b))

/-- The gluing isomorphism keeps the complete original retained chart comparison. -/
@[reassoc] theorem arithmeticClosingAttachmentIso_retained (b : Bool) :
    pushout.inl l (r b) ≫ (arithmeticClosingAttachmentIso data H m j hj u hu b).hom =
      (C).hom ≫ pushout.inl L (M b) := by
  simp [arithmeticClosingAttachmentIso]

/-- It also keeps the original full terminal normalization, including its smoothing factor. -/
@[reassoc] theorem arithmeticClosingAttachmentIso_terminal (b : Bool) :
    pushout.inr l (r b) ≫ (arithmeticClosingAttachmentIso data H m j hj u hu b).hom =
      (P).hom ≫ pushout.inr L (M b) := by
  simp [arithmeticClosingAttachmentIso]

end FLT.Mazur.WeierstrassDividedDepth
