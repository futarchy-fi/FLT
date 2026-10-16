/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroRetentionIntersection
public import FLT.Mazur.WeierstrassDividedArithmeticLabeledAtlas

/-!
# The full zero-retention boundary in the original arithmetic stage

The original initial/terminal overlap survives the global embedding and
arithmetic base change. Normalizing the terminal chart preserves the full
boundary and its actual initial projection.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
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

/-- The original global tensor maps retain the entire zero-retention overlap. -/
theorem zeroRetentionGlobalTensor_isPullback :
    IsPullback B (PrincipalOpenTensor.inclusion Q t)
      (globalDividedTensorChart hπ data Q 0 (Nat.zero_le n))
      (globalInitialTensorChart hπ data Q 0 (Nat.zero_le n)) := by
  have P := zeroRetentionFiniteTensor_isPullback hπ data Q
  exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _
    (finiteLocalTensorEmbedding hπ data Q 0 (Nat.zero_le n)) P.cone P.isLimit)

/-- Zero retention has a full original initial/terminal intersection at every arithmetic order. -/
theorem zeroRetentionArithmeticTensor_isPullback :
    IsPullback B (PrincipalOpenTensor.inclusion Q t) D I := by
  have P := zeroRetentionGlobalTensor_isPullback hπ data m
  exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _
    (pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap R Q)))
      (finiteGlobalStructure hπ data 0 (Nat.zero_le n))).hom P.cone P.isLimit)

variable (H : ArithmeticAtlasCoefficients data)
local notation "e" => WeierstrassDilatation.arithmeticTerminalNodeIso π m W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale 0) H.a2_div
    (H.b4_div _) (H.b6_div _)
local notation "c" => arithmeticLabeledAtlasMap hπ data H m 0 (Nat.zero_le n)

/-- Terminal normalization retains the whole zero-retention boundary to the original initial. -/
theorem zeroRetentionArithmeticNormalized_isPullback :
    IsPullback (B ≫ (e).inv) (PrincipalOpenTensor.inclusion Q t) (c .terminal) I := by
  apply (zeroRetentionArithmeticTensor_isPullback hπ data m).of_iso
    (Iso.refl _) (e).symm (Iso.refl _) (Iso.refl _)
  · simp
  · simp
  · simp [arithmeticLabeledAtlasMap, arithmeticLabeledTerminalChart]
  · simp

/-- The normalized zero-retention intersection is the actual complete arithmetic fiber product. -/
def zeroRetentionArithmeticNormalizedPullbackIso :
    Spec (.of (Localization.Away ((1 : Q) ⊗ₜ[R] t))) ≅ pullback (c .terminal) I :=
  (zeroRetentionArithmeticNormalized_isPullback hπ data m H).isoPullback

end FLT.Mazur.WeierstrassDividedDepth
