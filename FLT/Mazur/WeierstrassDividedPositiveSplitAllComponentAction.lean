/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitBoundaryComponentAction
public import FLT.Mazur.WeierstrassDividedPositiveSplitRetainedComponentAction
public import FLT.Mazur.WeierstrassDividedPositiveSplitExteriorScaling

/-!
# The actual coefficient action scales every original cyclic component

The exterior, initial, interior and terminal comparisons cover every cyclic
index, including both terminal branches and the shortest five-component polygon.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open MonoidalCategory CartesianMonoidalCategory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
open WeierstrassIntegralChart
local notation "𝕂" => ResidueField R
local notation "Z" => positiveSplitCycleComponent hπ data D s hs hstart hk hp
local notation "B" => finiteGlobalCoefficientOverAction hπ data (s + 1) hs 𝕂
local notation "v" => positiveSplitCyclicSmoothGroupIso D s hk

/-- The actual coefficient action is universal scaling on every complete component. -/
theorem positiveSplitCoefficientAction_component (i : Fin (2 * s + 5)) :
    ((v).hom.hom.hom.hom ⊗ₘ Z i) ≫ B =
      ProjectiveLineUniversalAction.act 𝕂 ≫ Z i := by
  by_cases hzero : i.val = 0
  · have hi : i = 0 := Fin.ext hzero
    rw [hi]
    exact positiveSplitCoefficientAction_exterior_scaling hπ data D s hs hstart hk hp
  by_cases hone : i.val = 1
  · have hi : i = 1 := Fin.ext hone
    rw [hi]
    exact positiveSplitCoefficientAction_firstComponent hπ data D s hs hstart hk hp
  by_cases hlast : i.val = 2 * s + 4
  · have hi : i = ⟨2 * s + 4, by omega⟩ := Fin.ext hlast
    rw [hi]
    exact positiveSplitCoefficientAction_lastComponent hπ data D s hs hstart hk hp
  by_cases hfirst : i.val < s + 3
  · let j : Fin (s + 1) := ⟨i.val - 2, by omega⟩
    have hi : i = ⟨j.val + 2, by omega⟩ := Fin.ext (by dsimp [j]; omega)
    rw [hi]
    exact positiveSplitCoefficientAction_retainedFirstComponent
      hπ data D s hs hstart hk hp j
  · let j : Fin (s + 1) := ⟨2 * s + 3 - i.val, by omega⟩
    have hi : i = ⟨2 * s + 4 - (j.val + 1), by omega⟩ := Fin.ext (by dsimp [j]; omega)
    rw [hi]
    exact positiveSplitCoefficientAction_retainedSecondComponent
      hπ data D s hs hstart hk hp j

end FLT.Mazur.WeierstrassDividedDepth
