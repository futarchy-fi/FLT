/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticFirstRetainedFactorRatio
public import FLT.Mazur.WeierstrassRetainedArithmeticFactorRatioRestriction

/-!
# The full first-retained comparison at both arithmetic labels

The source arrow is the original labeled atlas restriction. The target arrow
is the corrected polygon restriction with its exact normalized smoothing.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m k : ℕ) (hk : k ≤ n) (hk0 : 0 < k)
local notation "Q" => Quotient R π m
local notation "d₀" => data ⟨0, by omega⟩
local notation "d₁" => data ⟨1, by omega⟩
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ start) π m
local notation "hn" => Fact.mk
  (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ start) π m H.scale_div)
local notation "C" => arithmeticRetainedFactorRatioChart π m W (π ^ start)
  (Data.b3 d₁) (Data.b4 d₁) (Data.b6 d₁) H.a1_unit H.scale_div H.a2_div
  (H.b3_div _) (H.b4_div _) (H.b6_div _)
omit [IsBezout R] in
/-- Both full first-retained labels commute with the original arithmetic quotient diagrams. -/
@[reassoc] theorem arithmeticFactorRatioFirstRetainedMap_restriction (b : Bool) :
    arithmeticFactorRatioFirstRetainedMap hπ data H m k hk hk0 b ≫
      arithmeticFactorRatioPolygonRestriction π m W (π ^ start) H.a1_unit H.scale_div k =
    arithmeticLabeledAtlasRestriction hπ data H m k hk (.retained ⟨0, hk0⟩ b) ≫
      arithmeticFactorRatioFirstRetainedMap hπ data H (m + 1) k hk hk0 b := by
  let _ := hn
  let _ : Fact (IsNilpotent
      (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ start) π (m + 1))) :=
    ⟨arithmeticInitialFactorRatioSmoothing_nilpotent
      W H.a1_unit (π ^ start) π (m + 1) H.scale_div⟩
  unfold arithmeticFactorRatioFirstRetainedMap arithmeticFactorRatioPolygonRestriction
  rw [Category.assoc, retainedPolygonMap_parameterProjection,
    ← arithmeticRetainedFactorRatioChart_restriction_assoc]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
