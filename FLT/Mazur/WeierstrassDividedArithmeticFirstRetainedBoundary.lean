/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticFirstRetainedFactorRatio

/-!
# Agreement of the original initial and first retained arithmetic boundaries

Both Boolean labels use the original atlas objects and full Laurent maps.
The target is the exact corrected polygon, including every nilpotent term.
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
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ start) π m
local notation "hn" => Fact.mk
  (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ start) π m H.scale_div)
local notation "E" => arithmeticFactorRatioLaurentIso π m W (π ^ start)
  (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) H.a1_unit H.scale_div H.a2_div
  (H.b3_div _) (H.b4_div _) (H.b6_div _)

local notation "G" => arithmeticInitialNodeRestriction π m W (π ^ start)
  (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) H.a1_unit H.a2_div
  (H.b3_div _) (H.b4_div _) (H.b6_div _) H.scale_div

omit [IsBezout R] in
/-- The original initial Laurent leg agrees with the complete first retained labeled comparison. -/
@[reassoc] theorem arithmeticFactorRatioLabeledInitialMap_first_retained (b : Bool) :
    G ≫ arithmeticFactorRatioLabeledInitialMap data H hπ m k hk b =
      rightBranchOpen Q (parameter R π m) ≫
        arithmeticFactorRatioFirstRetainedMap hπ data H m k hk hk0 b := by
  let _ := hn
  rw [arithmeticFactorRatioLabeledInitialMap, arithmeticFactorRatioTensorAffineMap_chart,
    ← Category.assoc, arithmeticFactorRatioLaurentIso_boundary, Category.assoc,
    initialPolygonLabel_retained_boundary τ k hk0]
  exact (arithmeticFactorRatioFirstRetainedMap_right hπ data H m k hk hk0 b).symm

end FLT.Mazur.WeierstrassDividedDepth
