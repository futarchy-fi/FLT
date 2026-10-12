/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationShearNodeNormalForm
public import FLT.Mazur.WeierstrassCoefficientShearGluing
public import FLT.Mazur.PolygonCyclicCocone

/-!
# The full terminal node and both affine branches in the sheared equation gluing

The actual terminal coefficient equation gives an open node chart, with both
complete affine branches and their common origin. No projective component is
assumed in constructing these maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le hj))
variable (hs : algebraMap R S (π ^ (start + j)) = 0)
  (h3 : algebraMap R S (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (h6 : algebraMap R S (data ⟨j, Nat.lt_succ_of_le hj⟩).b6 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "e" => (coefficientShearNodeEquiv W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs h3 h4 h6 hr a ha).trans NodalFiber.polygonNodeEquiv
local notation "E" => Scheme.Spec.mapIso (e).toRingEquiv.toCommRingCatIso.op
local notation "G" => coefficientShearGluedIso hπ data S r j hj
local notation "base" => coefficientShearGluedStructure hπ data S r j hj

/-- The whole normalized terminal node is an actual chart of the coefficient model. -/
def coefficientShearTerminalNode : PolygonNodeBranches.node S ⟶
    coefficientShearGlued hπ data S r j hj :=
  (E).hom ≫ coefficientShearGluedChart hπ data S r j hj (.inl 1)

local notation "N" => coefficientShearTerminalNode hπ data S r j hj hs h3 h4 h6 hr a ha

instance coefficientShearTerminalNode_isOpenImmersion : IsOpenImmersion N :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- Reconstruction retains the entire original sheared divided equation. -/
@[reassoc] theorem coefficientShearTerminalNode_reconstruction :
    N ≫ (G).hom = (E).hom ≫ globalDividedCoefficientShearChart hπ data S r j hj := by
  rw [coefficientShearTerminalNode, Category.assoc, coefficientShearGluedIso_chart]
  rfl

/-- The full node chart keeps the actual extended coefficient structure. -/
@[reassoc] theorem coefficientShearTerminalNode_structure :
    N ≫ base = PolygonNodeBranches.toBase S := by
  rw [coefficientShearTerminalNode, Category.assoc, coefficientShearGluedChart_structure]
  exact algebraSpecIso_structure e

/-- The first complete terminal affine branch in the coefficient model. -/
def coefficientShearTerminalFirstBranch := PolygonCyclicAtlas.firstBranch S ≫ N

/-- The opposite complete terminal affine branch in the coefficient model. -/
def coefficientShearTerminalSecondBranch := PolygonCyclicAtlas.secondBranch S ≫ N

/-- The actual common terminal node section in the coefficient gluing. -/
def coefficientShearTerminalOrigin := PolygonNodePresentation.aOrigin S ≫ N

/-- The first full affine branch includes the actual terminal node at its origin. -/
@[reassoc] theorem coefficientShearTerminalFirstBranch_origin :
    ProjectiveLine.chartZero S ≫
        coefficientShearTerminalFirstBranch hπ data S r j hj hs h3 h4 h6 hr a ha =
      coefficientShearTerminalOrigin hπ data S r j hj hs h3 h4 h6 hr a ha := by
  rw [coefficientShearTerminalFirstBranch, ← Category.assoc,
    PolygonCyclicAtlas.zero_firstBranch]
  rfl

/-- The opposite full affine branch has the same terminal origin. -/
@[reassoc] theorem coefficientShearTerminalSecondBranch_origin :
    ProjectiveLine.chartZero S ≫
        coefficientShearTerminalSecondBranch hπ data S r j hj hs h3 h4 h6 hr a ha =
      coefficientShearTerminalOrigin hπ data S r j hj hs h3 h4 h6 hr a ha := by
  rw [coefficientShearTerminalSecondBranch, ← Category.assoc,
    PolygonCyclicAtlas.zero_secondBranch]
  rfl

/-- The first full branch preserves the actual coefficient-field projection. -/
@[reassoc] theorem coefficientShearTerminalFirstBranch_structure :
    coefficientShearTerminalFirstBranch hπ data S r j hj hs h3 h4 h6 hr a ha ≫ base =
      ProjectiveLine.chartToBase S := by
  rw [coefficientShearTerminalFirstBranch, Category.assoc,
    coefficientShearTerminalNode_structure, PolygonCyclicAtlas.firstBranch_toBase]

/-- The opposite full branch preserves the same coefficient projection. -/
@[reassoc] theorem coefficientShearTerminalSecondBranch_structure :
    coefficientShearTerminalSecondBranch hπ data S r j hj hs h3 h4 h6 hr a ha ≫ base =
      ProjectiveLine.chartToBase S := by
  rw [coefficientShearTerminalSecondBranch, Category.assoc,
    coefficientShearTerminalNode_structure, PolygonCyclicAtlas.secondBranch_toBase]

end FLT.Mazur.WeierstrassDividedDepth
