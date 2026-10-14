/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteNodeBranchLabels
public import FLT.Mazur.PolygonNodeLaurentPoints

/-!
# Actual primitive specialization in oriented Laurent coordinates

The original negative branch is parametrized by the residue of b, and the
positive branch by the residue of b + a₁a. These formulas identify the entire
proper specialization morphism, rather than just its underlying point.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j) ≤ depth)
  (hp : 2 * (start + j) < depth)
  (P : (W.map (algebraMap A K)).toProjective.Point)
  (v : NodePointCoordinates A W π P) (hv : v.depth = start + j)
local notation "F" => ResidueField A
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le hj))
local notation "ev" => finiteNodePointEvaluation A hπ data j hj P v hv
local notation "g" => WeierstrassDilatation.sectionNodeEvaluation D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
  (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp ev
local notation "p" => finiteOddNodePoint A data D j hj hk0 hk hp ev
local notation "c" => terminalNodeChart hπ data D j hj hk0 hk hp

/-- The negative-branch Laurent unit is the original primitive vertical residue. -/
def nodeNegativeLaurentUnit (hb : IsUnit v.b) : Fˣ := (hb.map (residue A)).unit

/-- The positive-branch Laurent unit is the other original tangent residue. -/
def nodePositiveLaurentUnit (hb : IsUnit (v.b + W.a₁ * v.a)) : Fˣ :=
  (hb.map (residue A)).unit

/-- The negative parameter keeps its original coordinate value. -/
theorem nodeNegativeLaurentUnit_val (hb : IsUnit v.b) :
    (nodeNegativeLaurentUnit A P v hb : F) = residue A v.b :=
  (hb.map (residue A)).unit_spec

/-- The positive parameter keeps its original coordinate value. -/
theorem nodePositiveLaurentUnit_val (hb : IsUnit (v.b + W.a₁ * v.a)) :
    (nodePositiveLaurentUnit A P v hb : F) = residue A (v.b + W.a₁ * v.a) :=
  (hb.map (residue A)).unit_spec

include D hk0 hp hv in
/-- The positive arithmetic branch supplies its actual Laurent unit. -/
theorem nodePositiveLaurent_isUnit (hb : v.b ∈ maximalIdeal A) :
    IsUnit (v.b + W.a₁ * v.a) := by
  have h := (node_point_branches_below_middle W D.uniformizer_ne_zero D.maximalIdeal_eq
    depth v.depth (by omega) (by omega) D.a₁_unit D.a₂_mem D.a₃_mem D.a₄_mem D.a₆_mem
    v.a v.b v.primitive v.equation).2
  exact h.elim (fun h => h.2) (fun h => False.elim (hb h.1))

/-- The actual node point is the Laurent point on its negative branch. -/
theorem finiteNodePoint_negative_laurent (hb : IsUnit v.b) :
    p = Spec.map (CommRingCat.ofHom
        (LaurentUnitPoints.evalUnit (R := F) (nodeNegativeLaurentUnit A P v hb)).toRingHom) ≫
      PolygonNodeBranches.left F := by
  apply PolygonNodeLaurentPoints.spec_left
  rw [finiteNodeEvaluation_x, nodeNegativeLaurentUnit_val]

/-- The actual node point is the Laurent point on its positive branch. -/
theorem finiteNodePoint_positive_laurent (hb : IsUnit (v.b + W.a₁ * v.a)) :
    p = Spec.map (CommRingCat.ofHom
        (LaurentUnitPoints.evalUnit (R := F) (nodePositiveLaurentUnit A P v hb)).toRingHom) ≫
      PolygonNodeBranches.right F := by
  apply PolygonNodeLaurentPoints.spec_right
  rw [finiteNodeEvaluation_y, nodePositiveLaurentUnit_val]

include hv in
/-- Negative Laurent coordinates reconstruct the unrestricted original specialization. -/
theorem finitePointSpecialization_negative_laurent (hb : IsUnit v.b) :
    finitePointSpecialization A hπ data j hj P =
      Spec.map (CommRingCat.ofHom
        (LaurentUnitPoints.evalUnit (R := F) (nodeNegativeLaurentUnit A P v hb)).toRingHom) ≫
        PolygonNodeBranches.left F ≫ c := by
  rw [← finiteNodePoint_specialization A hπ data D j hj hk0 hk hp P v hv,
    finiteNodePoint_negative_laurent, Category.assoc]

include hv in
/-- Positive Laurent coordinates reconstruct the unrestricted original specialization. -/
theorem finitePointSpecialization_positive_laurent (hb : IsUnit (v.b + W.a₁ * v.a)) :
    finitePointSpecialization A hπ data j hj P =
      Spec.map (CommRingCat.ofHom
        (LaurentUnitPoints.evalUnit (R := F) (nodePositiveLaurentUnit A P v hb)).toRingHom) ≫
        PolygonNodeBranches.right F ≫ c := by
  rw [← finiteNodePoint_specialization A hπ data D j hj hk0 hk hp P v hv,
    finiteNodePoint_positive_laurent, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
