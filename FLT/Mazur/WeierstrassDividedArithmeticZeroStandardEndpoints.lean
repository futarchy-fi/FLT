/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticZeroInitialEndpoints
public import FLT.Mazur.WeierstrassModificationXInitialTerminalPunctureIso

/-!
# The terminal side of the stage-zero initial endpoint comparisons

Both initial standard D(p) sources identify with the correct standard terminal
punctures, with their original Laurent parameter change and both projections.
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

/-- The standard initial puncture identifies with the correctly oriented terminal puncture. -/
def zeroRetentionInitialTerminalStandardIso :
    Spec (.of (Localization.Away (NodalFiber.p (q s)))) ≅
      Spec (.of (Localization.Away δ)) :=
  (P₀).symm.trans P₁

omit [IsBezout R] in
/-- The standard terminal inclusion is exactly the original endpoint map after parameter change. -/
@[reassoc] theorem zeroRetentionInitialTerminalStandardIso_terminal :
    (zeroRetentionInitialTerminalStandardIso data m H label).hom ≫ i =
      zeroRetentionInitialPunctureToTerminal hπ data m H label := by
  apply (cancel_epi (P₀).hom).mp
  rw [zeroRetentionInitialTerminalStandardIso, Iso.trans_hom, Iso.symm_hom,
    ← Category.assoc, Iso.hom_inv_id_assoc, initialTerminalArithmeticPunctureIso_boundary]
  rw [zeroRetentionInitialPunctureToTerminal]
  exact (arithmeticInitialPunctureIso_terminal_boundary π m W s
    (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _) label).symm

/-- Both full standard endpoint inclusions retain the original stage-zero labeled overlap. -/
@[reassoc] theorem zeroRetentionInitialTerminalStandardIso_overlap :
    (zeroRetentionInitialTerminalStandardIso data m H label).hom ≫ i ≫ c .terminal =
      P ≫ c (.initial label) := by
  rw [← Category.assoc, zeroRetentionInitialTerminalStandardIso_terminal,
    arithmeticLabeledAtlas_zero_initial_terminal_overlap]

/-- The stage-zero fiber product can be stated with the standard terminal puncture projection. -/
theorem arithmeticLabeledAtlas_zero_standard_terminal_isPullback :
    IsPullback ((zeroRetentionInitialTerminalStandardIso data m H label).hom ≫ i) P
      (c .terminal) (c (.initial label)) := by
  rw [zeroRetentionInitialTerminalStandardIso_terminal]
  exact arithmeticLabeledAtlas_zero_initial_terminal_isPullback hπ data m H label

end FLT.Mazur.WeierstrassDividedDepth
