/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticFixedAdjacentPuncture
public import FLT.Mazur.WeierstrassSuccessiveXArithmeticPuncturedBranches

/-!
# Branches of the actual fixed-stage adjacent target

The boundary range supplies its puncture, and the original arithmetic equation
supplies its branch. Neither condition is imposed again on the target point.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] arithmeticFixedAdjacentTargetCoordinates
  arithmeticFixedAdjacentBoundaryTarget globalTensorAtlasObject
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (m k : ℕ) (hk : k ≤ n) (j : ℕ) (hj : j + 2 ≤ k)
local notation "Q" => Quotient R π m
local notation "e" => data ⟨j + 2, by omega⟩
local notation "T" => ScalarExtension W (π ^ (start + (j + 1))) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q
local notation "u" => tensorCoord W (π ^ (start + (j + 1))) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 2
local notation "v" => tensorCoord W (π ^ (start + (j + 1))) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 1
local notation "α" => algebraMap R T W.a₁
local notation "ib" => (Fin.succ ⟨k - (j + 1), by omega⟩ : Fin (k + 3))
local notation "coords" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk j hj
local notation "boundary" => arithmeticFixedAdjacentBoundaryTarget hπ data m k hk j hj

include D in
/-- The actual adjacent boundary target forces one of the two contracted branches. -/
theorem arithmeticFixedAdjacentBoundaryTarget_branches
    (p : globalTensorAtlasObject hπ data Q k hk ib) (hp : p ∈ Set.range boundary) :
    u * v ∈ (coords p).asIdeal ∨ u * v + α * u ∈ (coords p).asIdeal := by
  exact arithmeticPunctured_contracted_cases D m (start + (j + 1))
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (by omega) (coords p)
    (arithmeticFixedAdjacentBoundaryTarget_punctured hπ data m k hk j hj p hp)

include D in
/-- The original target point cannot belong to both contracted branches. -/
theorem arithmeticFixedAdjacentBoundaryTarget_not_both
    (p : globalTensorAtlasObject hπ data Q k hk ib) (hp : p ∈ Set.range boundary) :
    ¬ (u * v ∈ (coords p).asIdeal ∧ u * v + α * u ∈ (coords p).asIdeal) := by
  exact arithmeticPunctured_contracted_not_both D m (start + (j + 1))
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (coords p)
    (arithmeticFixedAdjacentBoundaryTarget_punctured hπ data m k hk j hj p hp)

end FLT.Mazur.WeierstrassDividedDepth
