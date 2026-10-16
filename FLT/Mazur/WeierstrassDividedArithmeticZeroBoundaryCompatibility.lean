/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticZeroInitialEndpoints
public import FLT.Mazur.WeierstrassModificationXArithmeticPunctureCover

/-!
# Checking the full stage-zero boundary on both standard initial punctures

Compatibility of arbitrary scheme maps on the complete original
initial/terminal fiber product is equivalent to their two exact labeled
puncture equations. No function is reduced to its residue value.
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

local notation "P" => arithmeticInitialPunctureInclusion π m W (π ^ start) H.a1_unit H.scale_div
local notation "u" label => arithmeticInitialPunctureToTensorBoundary π m W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _) label H.scale_div

local notation "F" label => ite (label = true)
  (arithmeticOppositeInitialTensorNodeChart π m W (π ^ start)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _))
  (arithmeticInitialTensorNodeChart π m W (π ^ start)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _))

attribute [local irreducible] arithmeticInitialPunctureInclusion
  arithmeticInitialTensorNodeChart arithmeticOppositeInitialTensorNodeChart
  zeroRetentionInitialPunctureToTerminal arithmeticLabeledAtlasMap
  finiteArithmeticInitialTensorChart

/-- The complete initial tensor source at zero retention, before choosing either label. -/
abbrev zeroRetentionInitialTensorSource : Scheme :=
  Spec (.of (Q ⊗[R] WeierstrassModificationX.Coordinate W (π ^ start)
    (Data.b3 d) (Data.b4 d) (Data.b6 d)))

variable {Y : Scheme.{0}}
  (f : arithmeticLabeledAtlasObject hπ data H m 0 (Nat.zero_le n) .terminal ⟶ Y)
  (g : zeroRetentionInitialTensorSource data m ⟶ Y)

/-- Both exact initial puncture equations imply compatibility on the entire original boundary. -/
theorem zeroRetention_compatible_of_initial_punctures
    (h : ∀ label : Bool,
      zeroRetentionInitialPunctureToTerminal hπ data m H label ≫ f = P ≫ (F label) ≫ g) :
    pullback.fst (c .terminal) I ≫ f = pullback.snd (c .terminal) I ≫ g := by
  have T := zeroRetentionArithmeticNormalized_isPullback hπ data m H
  apply (cancel_epi T.isoPullback.hom).mp
  simp only [← Category.assoc, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd]
  apply arithmeticInitialPunctures_tensor_hom_ext π m W (π ^ start)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _) H.scale_div
  · simpa only [zeroRetentionInitialPunctureToTerminal, Category.assoc,
      arithmeticInitialPunctureToTensorBoundary_comp_assoc] using h false
  · simpa only [zeroRetentionInitialPunctureToTerminal, Category.assoc,
      arithmeticInitialPunctureToTensorBoundary_comp_assoc] using h true

/-- Full-boundary compatibility retains the original equation on every initial endpoint. -/
theorem zeroRetention_initial_punctures_of_compatible
    (h : pullback.fst (c .terminal) I ≫ f = pullback.snd (c .terminal) I ≫ g)
    (label : Bool) :
    zeroRetentionInitialPunctureToTerminal hπ data m H label ≫ f = P ≫ (F label) ≫ g := by
  have T := zeroRetentionArithmeticNormalized_isPullback hπ data m H
  have he := congrArg (fun z => T.isoPullback.hom ≫ z) h
  simp only [← Category.assoc, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd] at he
  have hl := congrArg (fun z => (u label) ≫ z) he
  simpa only [zeroRetentionInitialPunctureToTerminal, Category.assoc,
    arithmeticInitialPunctureToTensorBoundary_comp_assoc] using hl

/-- The complete stage-zero gluing condition is exactly the two original puncture equations. -/
theorem zeroRetention_compatible_iff_initial_punctures :
    (pullback.fst (c .terminal) I ≫ f = pullback.snd (c .terminal) I ≫ g) ↔
      ∀ label : Bool,
        zeroRetentionInitialPunctureToTerminal hπ data m H label ≫ f = P ≫ (F label) ≫ g :=
  ⟨fun h label => zeroRetention_initial_punctures_of_compatible hπ data m H f g h label,
    zeroRetention_compatible_of_initial_punctures hπ data m H f g⟩

end FLT.Mazur.WeierstrassDividedDepth
