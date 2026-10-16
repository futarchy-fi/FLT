/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticZeroStandardEndpoints

/-!
# Exact terminal compatibility for the two stage-zero labeled charts

Both standard terminal punctures retain their original parameter changes.
Their equations characterize the full labeled fiber products.
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

local notation "P" => arithmeticInitialPunctureInclusion π m W (π ^ start)
  H.a1_unit H.scale_div
local notation "γ" => WeierstrassDilatation.arithmeticTerminalSmoothing π m W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale 0) H.a2_div
    (H.b4_div _) (H.b6_div _)

/-- The standard terminal puncture projection in the original initial parameter. -/
def zeroRetentionStandardTerminalEndpoint (label : Bool) :=
  (zeroRetentionInitialTerminalStandardIso data m H label).hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap (NodalFiber.Coordinate γ)
      (Localization.Away (ite (label = true) (NodalFiber.p γ) (NodalFiber.q γ)))))

omit [IsBezout R] in
/-- The standard endpoint is the full original normalized boundary restriction. -/
@[reassoc] theorem zeroRetentionStandardTerminalEndpoint_eq (label : Bool) :
    zeroRetentionStandardTerminalEndpoint data m H label =
      zeroRetentionInitialPunctureToTerminal hπ data m H label :=
  zeroRetentionInitialTerminalStandardIso_terminal hπ data m H label

variable {Y : Scheme.{0}}
  (f : ∀ i, arithmeticLabeledAtlasObject hπ data H m 0 (Nat.zero_le n) i ⟶ Y)

/-- The two exact endpoint equations on the full standard terminal punctures. -/
def arithmeticZeroTerminalCompatible : Prop :=
  ∀ label : Bool, zeroRetentionStandardTerminalEndpoint data m H label ≫ f .terminal =
    P ≫ f (.initial label)

/-- Each standard terminal equation detects the entire original labeled fiber product. -/
theorem arithmeticZeroTerminal_endpoint_iff (label : Bool) :
    (pullback.fst (c .terminal) (c (.initial label)) ≫ f .terminal =
      pullback.snd (c .terminal) (c (.initial label)) ≫ f (.initial label)) ↔
    (zeroRetentionStandardTerminalEndpoint data m H label ≫ f .terminal =
      P ≫ f (.initial label)) := by
  have T := arithmeticLabeledAtlas_zero_initial_terminal_isPullback hπ data m H label
  rw [zeroRetentionStandardTerminalEndpoint_eq hπ]
  rw [← cancel_epi T.isoPullback.hom]
  simp only [← Category.assoc, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd]

/-- Both original terminal fiber-product conditions are exactly the standard endpoint equations. -/
theorem arithmeticZeroTerminal_compatible_iff :
    arithmeticZeroTerminalCompatible hπ data m H f ↔
      ∀ label : Bool,
        pullback.fst (c .terminal) (c (.initial label)) ≫ f .terminal =
          pullback.snd (c .terminal) (c (.initial label)) ≫ f (.initial label) := by
  unfold arithmeticZeroTerminalCompatible
  exact forall_congr' fun label =>
    (arithmeticZeroTerminal_endpoint_iff hπ data m H f label).symm

end FLT.Mazur.WeierstrassDividedDepth
