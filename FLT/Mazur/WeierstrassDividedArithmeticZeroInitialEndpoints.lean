/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticZeroRetentionIntersection
public import FLT.Mazur.WeierstrassModificationXArithmeticIncidencePullback

/-!
# The stage-zero initial endpoints in the full labeled arithmetic atlas

The initial labels meet the complete terminal node along their own standard
D(p). The terminal projection follows the original full modification overlap
and then the original terminal normalization, preserving every function.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "x" => WeierstrassDilatation.x W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "t" => WeierstrassModificationX.t W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "a" => WeierstrassModificationX.overlapEquiv W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "B" => Iso.hom (PrincipalOpenTensor.transitionIso Q x t a) ≫
  PrincipalOpenTensor.inclusion Q x
local notation "I" => finiteArithmeticInitialTensorChart hπ data m 0 (Nat.zero_le n)
local notation "D" => finiteArithmeticDividedTensorChart hπ data m 0 (Nat.zero_le n)

variable (H : ArithmeticAtlasCoefficients data)
local notation "e" => WeierstrassDilatation.arithmeticTerminalNodeIso π m W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale 0) H.a2_div
    (H.b4_div _) (H.b6_div _)
local notation "c" => arithmeticLabeledAtlasMap hπ data H m 0 (Nat.zero_le n)

variable (label : Bool)
local notation "P" => arithmeticInitialPunctureInclusion π m W (π ^ start) H.a1_unit H.scale_div
local notation "u" => arithmeticInitialPunctureToTensorBoundary π m W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _) label H.scale_div

/-- Each initial standard puncture maps through the unchanged full boundary to the terminal node. -/
def zeroRetentionInitialPunctureToTerminal :
    Spec (.of (Localization.Away (NodalFiber.p (algebraMap R Q (π ^ start))))) ⟶
      arithmeticLabeledAtlasObject hπ data H m 0 (Nat.zero_le n) .terminal :=
  u ≫ B ≫ (e).inv

/-- At zero retention each initial label meets the full terminal node along exactly D(p). -/
theorem arithmeticLabeledAtlas_zero_initial_terminal_isPullback :
    IsPullback (zeroRetentionInitialPunctureToTerminal hπ data m H label) P
      (c .terminal) (c (.initial label)) := by
  have H₁ := arithmeticInitialPunctureToTensorBoundary_isPullback π m W (π ^ start)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _) label H.scale_div
  have H₂ := zeroRetentionArithmeticNormalized_isPullback hπ data m H
  exact H₁.paste_horiz H₂

attribute [local irreducible] zeroRetentionInitialPunctureToTerminal arithmeticLabeledAtlasMap

/-- The full puncture keeps both original labeled chart maps in the zero-retention stage. -/
@[reassoc] theorem arithmeticLabeledAtlas_zero_initial_terminal_overlap :
    zeroRetentionInitialPunctureToTerminal hπ data m H label ≫ c .terminal =
      P ≫ c (.initial label) :=
  (arithmeticLabeledAtlas_zero_initial_terminal_isPullback hπ data m H label).w

/-- The standard initial puncture is the actual stage-zero labeled fiber product. -/
def zeroRetentionInitialTerminalPullbackIso :
    Spec (.of (Localization.Away (NodalFiber.p (algebraMap R Q (π ^ start))))) ≅
      pullback (c .terminal) (c (.initial label)) :=
  (arithmeticLabeledAtlas_zero_initial_terminal_isPullback hπ data m H label).isoPullback

/-- The fiber-product comparison preserves the full original terminal restriction. -/
@[reassoc] theorem zeroRetentionInitialTerminalPullbackIso_terminal :
    (zeroRetentionInitialTerminalPullbackIso hπ data m H label).hom ≫ pullback.fst _ _ =
      zeroRetentionInitialPunctureToTerminal hπ data m H label :=
  (arithmeticLabeledAtlas_zero_initial_terminal_isPullback hπ data m H label).isoPullback_hom_fst

/-- The fiber-product comparison preserves the initial D(p) inclusion. -/
@[reassoc] theorem zeroRetentionInitialTerminalPullbackIso_initial :
    (zeroRetentionInitialTerminalPullbackIso hπ data m H label).hom ≫ pullback.snd _ _ = P :=
  (arithmeticLabeledAtlas_zero_initial_terminal_isPullback hπ data m H label).isoPullback_hom_snd

end FLT.Mazur.WeierstrassDividedDepth
