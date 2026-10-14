/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearTerminalEquationDescent

/-!
# The terminal equation descent retains its original chart and coefficient maps

Both complete branches are the actual branches of the equation gluing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
local notation "d" => data ⟨j, Nat.lt_succ_of_le hj⟩
variable (hs : algebraMap R S (π ^ (start + j)) = 0)
  (h3 : algebraMap R S (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (h6 : algebraMap R S (data ⟨j, Nat.lt_succ_of_le hj⟩).b6 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "e" => (coefficientShearNodeEquiv W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs h3 h4 h6 hr a ha).trans NodalFiber.polygonNodeEquiv

local notation "E" => coefficientShearTerminalEquationIso data S r j hj hs h3 h4 h6 hr a ha
local notation "B₁" => coefficientShearTerminalEquationFirst data S r j hj hs h3 h4 h6 hr a ha
local notation "B₂" => coefficientShearTerminalEquationSecond data S r j hj hs h3 h4 h6 hr a ha
local notation "g" => coefficientShearAtlasStructure data S r j hj (.inl 1)

/-- The sealed original equation isomorphism retains its coefficient projection. -/
@[reassoc] theorem coefficientShearTerminalEquationIso_structure :
    (E).hom ≫ g = PolygonNodeBranches.toBase S := by
  rw [coefficientShearTerminalEquationIso]
  exact algebraSpecIso_structure e

/-- The first full equation branch is over the original coefficient field. -/
@[reassoc] theorem coefficientShearTerminalEquationFirst_structure :
    B₁ ≫ g = ProjectiveLine.chartToBase S := by
  rw [coefficientShearTerminalEquationFirst, Category.assoc,
    coefficientShearTerminalEquationIso_structure, PolygonCyclicAtlas.firstBranch_toBase]

/-- The opposite full equation branch has the same coefficient projection. -/
@[reassoc] theorem coefficientShearTerminalEquationSecond_structure :
    B₂ ≫ g = ProjectiveLine.chartToBase S := by
  rw [coefficientShearTerminalEquationSecond, Category.assoc,
    coefficientShearTerminalEquationIso_structure, PolygonCyclicAtlas.secondBranch_toBase]

/-- The original terminal descent is over the base whenever both input branches are. -/
theorem coefficientShearTerminalEquationDesc_structure
    {Y : Scheme.{u}} (f₁ f₂ : ProjectiveLine.chart S ⟶ Y)
    (w : ProjectiveLine.chartZero S ≫ f₁ = ProjectiveLine.chartZero S ≫ f₂)
    (b : Y ⟶ Spec (.of S))
    (h₁ : f₁ ≫ b = ProjectiveLine.chartToBase S)
    (h₂ : f₂ ≫ b = ProjectiveLine.chartToBase S) :
    coefficientShearTerminalEquationDesc data S r j hj hs h3 h4 h6 hr a ha f₁ f₂ w ≫ b = g := by
  apply coefficientShearTerminalEquation_hom_ext data S r j hj hs h3 h4 h6 hr a ha
  · rw [coefficientShearTerminalEquationDesc_first_assoc,
      coefficientShearTerminalEquationFirst_structure, h₁]
  · rw [coefficientShearTerminalEquationDesc_second_assoc,
      coefficientShearTerminalEquationSecond_structure, h₂]

variable [IsDomain R] [IsBezout R] (hπ : π ≠ 0)
local notation "A" => coefficientShearGluedChart hπ data S r j hj (.inl 1)

/-- The entire sealed equation isomorphism gives exactly the actual terminal node chart. -/
@[reassoc] theorem coefficientShearTerminalEquationIso_chart :
    (E).hom ≫ A = coefficientShearTerminalNode hπ data S r j hj hs h3 h4 h6 hr a ha := by
  rw [coefficientShearTerminalEquationIso, coefficientShearTerminalNode]

/-- The full first equation branch gives precisely the original first terminal branch. -/
@[reassoc] theorem coefficientShearTerminalEquationFirst_chart :
    B₁ ≫ A = coefficientShearTerminalFirstBranch hπ data S r j hj hs h3 h4 h6 hr a ha := by
  rw [coefficientShearTerminalEquationFirst, Category.assoc,
    coefficientShearTerminalEquationIso_chart]
  rfl

/-- The full opposite equation branch gives precisely the original second terminal branch. -/
@[reassoc] theorem coefficientShearTerminalEquationSecond_chart :
    B₂ ≫ A = coefficientShearTerminalSecondBranch hπ data S r j hj hs h3 h4 h6 hr a ha := by
  rw [coefficientShearTerminalEquationSecond, Category.assoc,
    coefficientShearTerminalEquationIso_chart]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
