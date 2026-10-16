/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticZeroBoundaryCompatibility
public import FLT.Mazur.WeierstrassDividedArithmeticZeroStandardEndpoints

/-!
# Complete stage-zero compatibility in standard terminal parameters

The binary boundary criterion retains the full standard terminal punctures
and their constructed parameter changes, including both original initial labels.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct LaurentPolynomial
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

local notation "s" => π ^ start
local notation "q" => algebraMap R Q
local notation "γ" => WeierstrassDilatation.arithmeticTerminalSmoothing π m W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale 0) H.a2_div
    (H.b4_div _) (H.b6_div _)
local notation "δ" => ite (label = true) (NodalFiber.p γ) (NodalFiber.q γ)
local notation "i" => Spec.map (CommRingCat.ofHom
  (algebraMap (NodalFiber.Coordinate γ) (Localization.Away δ)))
local notation "P₀" => arithmeticInitialPunctureIso π m W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "P₁" => initialTerminalArithmeticPunctureIso π m W s
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _) label

attribute [local irreducible] arithmeticInitialPunctureIso initialTerminalArithmeticPunctureIso
  zeroRetentionInitialPunctureToTerminal

variable {Y : Scheme.{0}}
  (f : arithmeticLabeledAtlasObject hπ data H m 0 (Nat.zero_le n) .terminal ⟶ Y)
  (g : zeroRetentionInitialTensorSource data m ⟶ Y)
local notation "F" b => ite (b = true)
  (arithmeticOppositeInitialTensorNodeChart π m W s
    (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _))
  (arithmeticInitialTensorNodeChart π m W s
    (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _))

omit [IsBezout R] in
/-- Each original puncture equation is exactly its full standard terminal equation. -/
theorem zeroRetention_standard_endpoint_iff :
    ((zeroRetentionInitialTerminalStandardIso data m H label).hom ≫ i ≫ f =
      P ≫ (F label) ≫ g) ↔
    (zeroRetentionInitialPunctureToTerminal hπ data m H label ≫ f =
      P ≫ (F label) ≫ g) := by
  rw [← Category.assoc, zeroRetentionInitialTerminalStandardIso_terminal]

/-- Both full standard terminal endpoints detect the complete stage-zero gluing equation. -/
theorem zeroRetention_compatible_iff_standard_endpoints :
    (pullback.fst (c .terminal) I ≫ f = pullback.snd (c .terminal) I ≫ g) ↔
      ∀ label : Bool,
        (zeroRetentionInitialTerminalStandardIso data m H label).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap (NodalFiber.Coordinate γ)
            (Localization.Away (ite (label = true) (NodalFiber.p γ) (NodalFiber.q γ))))) ≫ f =
          P ≫ (F label) ≫ g := by
  rw [zeroRetention_compatible_iff_initial_punctures]
  exact forall_congr' fun label =>
    (zeroRetention_standard_endpoint_iff hπ data m H label f g).symm

end FLT.Mazur.WeierstrassDividedDepth
