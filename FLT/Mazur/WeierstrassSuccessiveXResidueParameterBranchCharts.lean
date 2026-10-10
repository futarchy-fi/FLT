/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleParameterBranchCharts
public import FLT.Mazur.WeierstrassSuccessiveXResidueSplitBranchCharts

/-!
# Original localized branches in the tensor residue fiber

The conic and horizontal restrictions hold at arbitrary divided constant,
including the last retained equality-depth conic.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "W₀" => W.map (residue R)
local notation "c" => residue R b6
local notation "a" => residue R W.a₁
local notation "h2" => Iff.mpr (residue_eq_zero_iff _) D.a₂_mem
local notation "ha" => D.a₁_unit.map (residue R)

local notation "C₁" => residueSuccessiveConicImmersion D k hk0 hk b3 b4 b6 h3 h4
local notation "L" => residueSuccessiveLineImmersion D k hk0 hk b3 b4 b6 h3 h4

/-- The first conic branch is its original full parameter in the tensor fiber. -/
@[reassoc] theorem residueMiddleFirstNodeChart_parameterConicBranch :
    middleParameterConicBranch c ≫ residueMiddleFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4 =
      (conicFirstParameterIso a c ha).inv ≫
        conicFirstOpenImmersion a c ≫ C₁ := by
  rw [residueMiddleFirstNodeChart_retained, ← Category.assoc,
    middleParameterConicBranch_firstChart]
  simp only [residueSuccessiveConicImmersion, Category.assoc, WeierstrassCurve.map]

/-- The opposite conic branch preserves the required negative second parameter. -/
@[reassoc] theorem residueMiddleSecondNodeChart_parameterConicBranch :
    middleParameterConicBranch c ≫ residueMiddleSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4 =
      Spec.map (CommRingCat.ofHom (conicParameterNeg c).toRingHom) ≫
        (conicSecondParameterIso a c ha).inv ≫
          conicSecondOpenImmersion a c ≫ C₁ := by
  rw [residueMiddleSecondNodeChart_retained, ← Category.assoc,
    middleParameterConicBranch_secondChart]
  simp only [residueSuccessiveConicImmersion, Category.assoc, WeierstrassCurve.map]

/-- The first horizontal branch retains its original tensor line map. -/
@[reassoc] theorem residueMiddleFirstNodeChart_parameterLineBranch :
    middleParameterLineBranch c ≫ residueMiddleFirstNodeChart D k hk0 hk b3 b4 b6 h3 h4 =
      L 0 (middle_first_root W₀) := by
  rw [residueMiddleFirstNodeChart_retained, ← Category.assoc,
    middleParameterLineBranch_firstChart]
  rfl

/-- The opposite horizontal branch retains its original translated slope. -/
@[reassoc] theorem residueMiddleSecondNodeChart_parameterLineBranch :
    middleParameterLineBranch c ≫ residueMiddleSecondNodeChart D k hk0 hk b3 b4 b6 h3 h4 =
      L (-a) (middle_second_root W₀) := by
  rw [residueMiddleSecondNodeChart_retained, ← Category.assoc,
    middleParameterLineBranch_secondChart]
  rfl

end FLT.Mazur.WeierstrassSuccessiveX
