/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteOddSpecialization
public import FLT.Mazur.EllipticFiniteNodeBoundarySection
public import FLT.Mazur.EllipticNodeLabelDecode
public import FLT.Mazur.WeierstrassDilatationSectionNodeCoordinates

/-!
# Arithmetic labels of the actual normalized node point

At every positive strict depth, the two actual punctured branches are exactly
the negative and positive arithmetic labels. Their coordinates are computed
from the original primitive point, without choosing a replacement specialization.
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

/-- The actual first tangent value is the residue of the primitive vertical coordinate. -/
theorem finiteNodeEvaluation_x : g PolygonNodeLocalization.x = residue A v.b := by
  rw [WeierstrassDilatation.sectionNodeEvaluation_x]
  change residue A (WeierstrassDilatation.evaluation W _ _ _ _ v.a v.b _ _) = _
  rw [WeierstrassDilatation.evaluation_y]

/-- The actual second tangent value is the residue of the other primitive tangent factor. -/
theorem finiteNodeEvaluation_y :
    g PolygonNodeLocalization.y = residue A (v.b + W.a₁ * v.a) := by
  rw [WeierstrassDilatation.sectionNodeEvaluation_y]
  change residue A (WeierstrassDilatation.evaluation W _ _ _ _ v.a v.b _ _ +
    W.a₁ * WeierstrassDilatation.evaluation W _ _ _ _ v.a v.b _ _) = _
  rw [WeierstrassDilatation.evaluation_y, WeierstrassDilatation.evaluation_x]

/-- The normalized point includes as the unrestricted proper specialization at its depth. -/
@[reassoc] theorem finiteNodePoint_specialization :
    p ≫ terminalNodeChart hπ data D j hj hk0 hk hp =
      finitePointSpecialization A hπ data j hj P := by
  rw [finiteOddNodePoint_inclusion]
  exact finitePointSpecialization_nodeChart A hπ data j hj P v hv

/-- The first geometric branch occurs exactly when the original vertical coordinate is a unit. -/
theorem finiteNodePoint_left_iff (z : Spec (.of F)) :
    p z ∈ Set.range (PolygonNodeBranches.left F) ↔ IsUnit v.b := by
  rw [PolygonNodeBranches.range_left]
  change g PolygonNodeLocalization.x ∉ z.asIdeal ↔ _
  let _ := z.isPrime
  rw [show z.asIdeal = ⊥ from Ideal.eq_bot_of_prime z.asIdeal]
  change g PolygonNodeLocalization.x ≠ 0 ↔ _
  rw [finiteNodeEvaluation_x, residue_ne_zero_iff_isUnit]

/-- The opposite geometric branch is exactly the first arithmetic tangent branch. -/
theorem finiteNodePoint_right_iff (z : Spec (.of F)) :
    p z ∈ Set.range (PolygonNodeBranches.right F) ↔ v.b ∈ maximalIdeal A := by
  rw [PolygonNodeBranches.range_right]
  change g PolygonNodeLocalization.y ∉ z.asIdeal ↔ _
  let _ := z.isPrime
  rw [show z.asIdeal = ⊥ from Ideal.eq_bot_of_prime z.asIdeal]
  change g PolygonNodeLocalization.y ≠ 0 ↔ _
  have hb := WeierstrassDilatation.sectionNodeEvaluation_horizontal_branches D
    (start + j) hk0 hk (Data.b3 d) (Data.b4 d) (Data.b6 d)
    (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp ev
    (finiteNodePoint_horizontal_unit A hπ data D j hj hk0 hp P v hv)
  rw [← residue_eq_zero_iff, ← finiteNodeEvaluation_x A hπ data D j hj hk0 hk hp P v hv]
  rcases hb with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact ⟨fun _ => hx, fun _ => hy⟩
  · exact ⟨fun h => False.elim (h hy), fun h => False.elim (hx h)⟩

/-- The first geometric branch carries the negative arithmetic label. -/
theorem finiteNodePoint_left_label (z : Spec (.of F)) :
    p z ∈ Set.range (PolygonNodeBranches.left F) ↔
      nodePointLabel D P = -((start + j : ℕ) : ZMod depth) := by
  rw [finiteNodePoint_left_iff, nodePointLabel_eq_of_coordinates D v]
  constructor
  · intro hb
    rw [hv]
    exact nodeBranchLabel_of_unit (by omega) hb
  · intro he
    exact (nodeBranchLabel_decode_negative D.depth_pos hk0 hp (by omega) v.b he).2

/-- The second geometric branch carries the positive arithmetic label. -/
theorem finiteNodePoint_right_label (z : Spec (.of F)) :
    p z ∈ Set.range (PolygonNodeBranches.right F) ↔
      nodePointLabel D P = ((start + j : ℕ) : ZMod depth) := by
  rw [finiteNodePoint_right_iff, nodePointLabel_eq_of_coordinates D v]
  constructor
  · intro hb
    rw [hv]
    exact nodeBranchLabel_of_mem depth (start + j) hb
  · intro he
    exact (nodeBranchLabel_decode_positive D.depth_pos hk0 (by omega)
      (by omega) v.b he).2.resolve_left (by omega)

end FLT.Mazur.WeierstrassDividedDepth
