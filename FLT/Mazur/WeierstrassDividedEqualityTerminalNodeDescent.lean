/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedEqualityTerminalNodeParameters
public import FLT.Mazur.WeierstrassSuccessiveXMiddleParameterDescent

/-!
# Descent from the complete equality-depth terminal component

Maps from the terminal projective line and a horizontal branch descend to
each original middle attachment. Only agreement at the actual endpoint is
required; targets are arbitrary schemes and horizontal scales are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth) (hp : 2 * (start + j + 1) = depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 e)
local notation "q₁" => equalityTerminalFirstNodeParameter data D j hj hk hp
local notation "q₂" => equalityTerminalSecondNodeParameter data D j hj hk hp
local notation "o" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicParameterOrigin c)))
local notation "ν" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (AlgEquiv.toAlgHom (conicParameterNeg c))))

/-- Compatible first endpoint data descend uniquely on the full original middle node. -/
theorem equalityTerminalFirstNode_exists_unique_desc (a : Kˣ) {Y : Scheme.{u}}
    (f : ProjectiveLine.scheme K ⟶ Y) (g : ProjectiveLine.chart K ⟶ Y)
    (w : ProjectiveLine.zero K ≫ f = ProjectiveLine.chartZero K ≫ g) :
    ∃! d : Spec (.of (MiddleNodeOpen c)) ⟶ Y,
      middleParameterConicBranch c ≫ d = q₁ ≫ f ∧
      ProjectiveLine.chartScaling K a ≫ middleParameterLineBranch c ≫ d = g := by
  have w' : o ≫ q₁ ≫ f = ProjectiveLine.chartZero K ≫ g := by
    rw [equalityTerminalFirstNodeParameter_origin_assoc]
    exact w
  exact middleParameter_exists_unique_scaled_desc c a (q₁ ≫ f) g w'

/-- Compatible opposite endpoint data descend with the original signed parameter. -/
theorem equalityTerminalSecondNode_exists_unique_desc (a : Kˣ) {Y : Scheme.{u}}
    (f : ProjectiveLine.scheme K ⟶ Y) (g : ProjectiveLine.chart K ⟶ Y)
    (w : ProjectiveLine.infinity K ≫ f = ProjectiveLine.chartZero K ≫ g) :
    ∃! d : Spec (.of (MiddleNodeOpen c)) ⟶ Y,
      middleParameterConicBranch c ≫ d = ν ≫ q₂ ≫ f ∧
      ProjectiveLine.chartScaling K a ≫ middleParameterLineBranch c ≫ d = g := by
  have w' : o ≫ ν ≫ q₂ ≫ f = ProjectiveLine.chartZero K ≫ g := by
    rw [middleParameterNeg_origin_assoc, equalityTerminalSecondNodeParameter_origin_assoc]
    exact w
  exact middleParameter_exists_unique_scaled_desc c a (ν ≫ q₂ ≫ f) g w'

end FLT.Mazur.WeierstrassDividedDepth
