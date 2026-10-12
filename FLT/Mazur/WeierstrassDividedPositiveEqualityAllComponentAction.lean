/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityBoundaryComponentAction
public import FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorComponentAction
public import FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalComponentAction
public import FLT.Mazur.WeierstrassDividedPositiveEqualityExteriorScaling

/-!
# The actual coefficient action scales every original cyclic component

The exterior, initial, interior and terminal comparisons cover every cyclic
index, including the shortest polygon where both interior chains are empty.
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
  (hp : 2 * (start + s + 1) = depth)
open WeierstrassIntegralChart
local notation "𝕂" => ResidueField R
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
local notation "B" => finiteGlobalCoefficientOverAction hπ data (s + 1) hs 𝕂
local notation "v" => positiveEqualityCyclicSmoothGroupIso D s hk

/-- The actual coefficient action is universal scaling on every complete component. -/
theorem positiveEqualityCoefficientAction_component (i : Fin (2 * s + 4)) :
    ((v).hom.hom.hom.hom ⊗ₘ Z i) ≫ B =
      ProjectiveLineUniversalAction.act 𝕂 ≫ Z i := by
  by_cases hzero : i.val = 0
  · have hi : i = 0 := Fin.ext hzero
    rw [hi]
    exact positiveEqualityCoefficientAction_exterior_scaling hπ data D s hs hstart hk hp
  by_cases hone : i.val = 1
  · have hi : i = 1 := Fin.ext hone
    rw [hi]
    exact positiveEqualityCoefficientAction_firstComponent hπ data D s hs hstart hk hp
  by_cases hterminal : i.val = s + 2
  · have hi : i = ⟨s + 2, by omega⟩ := Fin.ext hterminal
    rw [hi]
    exact positiveEqualityCoefficientAction_terminalComponent hπ data D s hs hstart hk hp
  by_cases hlast : i.val = 2 * s + 3
  · have hi : i = ⟨2 * s + 3, by omega⟩ := Fin.ext hlast
    rw [hi]
    exact positiveEqualityCoefficientAction_lastComponent hπ data D s hs hstart hk hp
  by_cases hfirst : i.val < s + 2
  · let j : Fin s := ⟨i.val - 2, by omega⟩
    have hi : i = ⟨j.val + 2, by omega⟩ := Fin.ext (by dsimp [j]; omega)
    rw [hi]
    exact positiveEqualityCoefficientAction_interiorFirstComponent
      hπ data D s hs hstart hk hp j
  · let j : Fin s := ⟨2 * s + 2 - i.val, by omega⟩
    have hi : i = ⟨2 * s + 2 - j.val, by omega⟩ := Fin.ext (by dsimp [j]; omega)
    rw [hi]
    exact positiveEqualityCoefficientAction_interiorSecondComponent
      hπ data D s hs hstart hk hp j

end FLT.Mazur.WeierstrassDividedDepth
