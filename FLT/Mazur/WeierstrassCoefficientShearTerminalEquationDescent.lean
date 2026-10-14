/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearTerminalNode
public import FLT.Mazur.NodePinchingDescent

/-!
# Arbitrary-target descent on the full sheared terminal equation

The actual coefficient equation is a node. Its two complete affine branches
therefore descend uniquely, without an affine hypothesis on the target.
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

/-- The original divided coefficient equation, sealed as an isomorphism from the node. -/
@[irreducible] def coefficientShearTerminalEquationIso : PolygonNodeBranches.node S ≅
    coefficientShearAtlasObject data S r j hj (.inl 1) :=
  Scheme.Spec.mapIso (e).toRingEquiv.toCommRingCatIso.op
local notation "E" => coefficientShearTerminalEquationIso data S r j hj hs h3 h4 h6 hr a ha

/-- The first entire branch in the actual terminal equation. -/
def coefficientShearTerminalEquationFirst : ProjectiveLine.chart S ⟶
    coefficientShearAtlasObject data S r j hj (.inl 1) :=
  PolygonCyclicAtlas.firstBranch S ≫ (E).hom

/-- The opposite entire branch in the same equation. -/
def coefficientShearTerminalEquationSecond : ProjectiveLine.chart S ⟶
    coefficientShearAtlasObject data S r j hj (.inl 1) :=
  PolygonCyclicAtlas.secondBranch S ≫ (E).hom
local notation "B₁" => coefficientShearTerminalEquationFirst data S r j hj hs h3 h4 h6 hr a ha
local notation "B₂" => coefficientShearTerminalEquationSecond data S r j hj hs h3 h4 h6 hr a ha

/-- The two entire original terminal branches detect morphisms to arbitrary schemes. -/
theorem coefficientShearTerminalEquation_hom_ext {Y : Scheme.{u}}
    (f g : coefficientShearAtlasObject data S r j hj (.inl 1) ⟶ Y)
    (h₁ : B₁ ≫ f = B₁ ≫ g) (h₂ : B₂ ≫ f = B₂ ≫ g) : f = g := by
  apply (cancel_epi (E).hom).mp
  apply NodePinchingDescent.hom_ext S
  · simpa only [coefficientShearTerminalEquationFirst, Category.assoc] using h₁
  · simpa only [coefficientShearTerminalEquationSecond, Category.assoc] using h₂

variable {Y : Scheme.{u}} (f g : ProjectiveLine.chart S ⟶ Y)
  (w : ProjectiveLine.chartZero S ≫ f = ProjectiveLine.chartZero S ≫ g)

/-- Compatible complete affine inputs descend to the full original terminal equation. -/
@[irreducible] def coefficientShearTerminalEquationDesc :
    coefficientShearAtlasObject data S r j hj (.inl 1) ⟶ Y :=
  (E).inv ≫ (NodePinchingDescent.node_desc S f g w).choose
local notation "D" => coefficientShearTerminalEquationDesc
  data S r j hj hs h3 h4 h6 hr a ha f g w

/-- Descent recovers the full first affine input. -/
@[reassoc] theorem coefficientShearTerminalEquationDesc_first : B₁ ≫ D = f := by
  rw [coefficientShearTerminalEquationFirst, coefficientShearTerminalEquationDesc,
    Category.assoc, Iso.hom_inv_id_assoc]
  exact (NodePinchingDescent.node_desc S f g w).choose_spec.1.1

/-- Descent recovers the full opposite affine input. -/
@[reassoc] theorem coefficientShearTerminalEquationDesc_second : B₂ ≫ D = g := by
  rw [coefficientShearTerminalEquationSecond, coefficientShearTerminalEquationDesc,
    Category.assoc, Iso.hom_inv_id_assoc]
  exact (NodePinchingDescent.node_desc S f g w).choose_spec.1.2

/-- These two entire branch restrictions uniquely characterize the equation descent. -/
theorem coefficientShearTerminalEquationDesc_unique
    (m : coefficientShearAtlasObject data S r j hj (.inl 1) ⟶ Y)
    (h₁ : B₁ ≫ m = f) (h₂ : B₂ ≫ m = g) : m = D := by
  apply coefficientShearTerminalEquation_hom_ext data S r j hj hs h3 h4 h6 hr a ha
  · exact h₁.trans (coefficientShearTerminalEquationDesc_first
      data S r j hj hs h3 h4 h6 hr a ha f g w).symm
  · exact h₂.trans (coefficientShearTerminalEquationDesc_second
      data S r j hj hs h3 h4 h6 hr a ha f g w).symm

end FLT.Mazur.WeierstrassDividedDepth
