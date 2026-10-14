/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteNodeLaurentSpecialization
public import FLT.Mazur.EllipticFiniteRetainedSpecialization
public import FLT.Mazur.WeierstrassHorizontalBranchRestriction
public import FLT.Mazur.PrincipalOpenTensorEvaluation

/-!
# Actual primitive points on retained horizontal Laurent branches

The original tangent units reconstruct the entire horizontal tensor evaluation.
Cancellation uses the actual open inclusion and preserves both divided functions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped TensorProduct
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
local notation "B" => WeierstrassDilatation.HorizontalCoordinate W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "ev" => finiteNodePointEvaluation A hπ data j hj P v hv
local notation "b" => finiteNodeBoundaryEvaluation A hπ data D j hj hk0 hp P v hv
local notation "g" => AlgHom.liftEquiv A F B F (AlgHom.comp (IsScalarTower.toAlgHom A A F) b)
local notation "N" => WeierstrassDilatation.residueNodeIso D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "p" => finiteOddNodePoint A data D j hj hk0 hk hp ev
local notation "l" => WeierstrassDilatation.residueHorizontalLeft D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "r" => WeierstrassDilatation.residueHorizontalRight D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp

/-- The horizontal tensor evaluation restricts to the original normalized node point. -/
@[reassoc] theorem finiteNodeBoundaryEvaluation_tensor_inclusion :
    Spec.map (CommRingCat.ofHom (g).toRingHom) ≫
      PrincipalOpenTensor.tensorInclusion (R := A) F x = p ≫ (N).hom := by
  rw [finiteOddNodePoint, WeierstrassDilatation.sectionNodeEvaluation_inclusion]
  apply PrincipalOpenTensor.evaluation_inclusion
  intro z
  change residue A (b (algebraMap _ B z)) = residue A (ev z)
  rw [finiteNodeBoundaryEvaluation_base]

/-- The original negative tangent unit gives the full retained horizontal evaluation. -/
theorem finiteNodeBoundaryEvaluation_negative_laurent (hb : IsUnit v.b) :
    Spec.map (CommRingCat.ofHom
        (LaurentUnitPoints.evalUnit (R := F) (nodeNegativeLaurentUnit A P v hb)).toRingHom) ≫
      l = Spec.map (CommRingCat.ofHom (g).toRingHom) := by
  apply (cancel_mono (PrincipalOpenTensor.tensorInclusion (R := A) F x)).mp
  rw [Category.assoc, WeierstrassDilatation.residueHorizontalLeft_inclusion,
    finiteNodeBoundaryEvaluation_tensor_inclusion,
    finiteNodePoint_negative_laurent, Category.assoc]

/-- The original positive tangent unit gives the full retained horizontal evaluation. -/
theorem finiteNodeBoundaryEvaluation_positive_laurent (hb : IsUnit (v.b + W.a₁ * v.a)) :
    Spec.map (CommRingCat.ofHom
        (LaurentUnitPoints.evalUnit (R := F) (nodePositiveLaurentUnit A P v hb)).toRingHom) ≫
      r = Spec.map (CommRingCat.ofHom (g).toRingHom) := by
  apply (cancel_mono (PrincipalOpenTensor.tensorInclusion (R := A) F x)).mp
  rw [Category.assoc, WeierstrassDilatation.residueHorizontalRight_inclusion,
    finiteNodeBoundaryEvaluation_tensor_inclusion,
    finiteNodePoint_positive_laurent, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
