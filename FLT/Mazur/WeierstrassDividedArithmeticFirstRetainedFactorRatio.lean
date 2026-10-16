/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedArithmeticFactorRatio
public import FLT.Mazur.WeierstrassDividedArithmeticFactorRatioLabeledMaps
public import FLT.Mazur.WeierstrassDividedFactorRatioRetainedBoundary

/-!
# The first retained comparison on the original arithmetic labeled atlas

Consecutive data force the divided coefficient identities. The constructed
map uses the exact normalized smoothing and both original retained labels.
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
local notation "E" => arithmeticFactorRatioLaurentIso π m W (π ^ start)
  (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) H.a1_unit H.scale_div H.a2_div
  (H.b3_div _) (H.b4_div _) (H.b6_div _)

/-- The first retained node maps to the corrected polygon at each of its original labels. -/
def arithmeticFactorRatioFirstRetainedMap (b : Bool) :
    arithmeticLabeledAtlasObject hπ data H m k hk (.retained ⟨0, hk0⟩ b) ⟶
      arithmeticFactorRatioPolygon π m W (π ^ start) H.a1_unit H.scale_div k := by
  let _ := hn
  exact C ≫ retainedPolygonMap Q τ k ⟨0, hk0⟩ b

omit [IsBezout R] in
include hπ in
/-- Consecutive data identify the full right parameter with the original initial one. -/
@[reassoc] theorem arithmeticFirstRetainedFactorRatioChart_right :
    rightBranchOpen Q (parameter R π m) ≫ C =
      (E).hom ≫ (edgeInversion Q).hom ≫ rightBranchOpen Q τ := by
  apply arithmeticRetainedFactorRatioChart_right_of_eq
  · exact factor3_step hπ d₀ d₁
  · exact factor4_step hπ d₀ d₁
  · exact factor6_step hπ d₀ d₁

omit [IsBezout R] in
/-- The entire first retained boundary reaches the exact original corrected cyclic label. -/
@[reassoc] theorem arithmeticFactorRatioFirstRetainedMap_right (b : Bool) :
    rightBranchOpen Q (parameter R π m) ≫
      arithmeticFactorRatioFirstRetainedMap hπ data H m k hk hk0 b =
        (E).hom ≫ precedingBranch Q τ ≫ @retainedPolygonMap Q _ τ hn k ⟨0, hk0⟩ b := by
  unfold arithmeticFactorRatioFirstRetainedMap
  rw [← Category.assoc, arithmeticFirstRetainedFactorRatioChart_right hπ data H m k hk hk0]
  simp only [precedingBranch, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
