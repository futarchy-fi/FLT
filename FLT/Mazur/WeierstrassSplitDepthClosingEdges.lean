/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitDepthRetainedComparison
public import FLT.Mazur.WeierstrassRetainedFixedTerminalEdges
public import FLT.Mazur.WeierstrassDividedRetainedClosingUnit

/-!
# The actual split-depth retained closing maps

The full parameters and terminal polygon indices are constructed from the
original split coefficient data. Both Boolean labels retain their orientation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (j : ℕ) (hn : 2 * (1 + (j + 1)) < depth) (m : ℕ)
local notation "d" => splitDepthStartOneData D (j + 1) hn
local notation "H" => splitDepthStartOneAtlasCoefficients D (j + 1) hn
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W D.a₁_unit (π ^ 1) π m
local notation "V" => arithmeticRetainedFullCorrection d H m (j + 1) le_rfl
  (Fin.mk j (Nat.lt_succ_self j))
local notation "q" => arithmeticStartOneQuotient W D.a₁_unit π m
local notation "u" => arithmeticRetainedClosingUnit d H m (j + 1) le_rfl
  (Fin.mk j (Nat.lt_succ_self j))

/-- Every actual last retained map lands in its specified puncture of terminal index zero. -/
@[reassoc] theorem splitDepthRetainedComparison_last (b : Bool) :
    let _ := Fact.mk (arithmeticInitialFactorRatioSmoothing_nilpotent W D.a₁_unit
      (π ^ 1) π m (H).scale_div)
    leftBranchOpen Q (parameter R π m) ≫
        splitDepthRetainedComparison D (j + 1) hn m (j + 1) le_rfl ⟨j, by omega⟩ b =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := Q) u).toRingHom) ≫
        (if b then leftBranchOpen Q τ else rightBranchOpen Q τ) ≫
          PolygonInfinitesimal.chart Q τ (2 * (j + 1) + 3) (by omega) 0 := by
  let _ := Fact.mk (arithmeticInitialFactorRatioSmoothing_nilpotent W D.a₁_unit
    (π ^ 1) π m (H).scale_div)
  exact retainedFixedPolygonMap_last (parameter R π m) τ q
    (arithmeticStartOneQuotient_relation W (H).a1_unit π m) 1 j V b

end FLT.Mazur.WeierstrassDividedDepth
