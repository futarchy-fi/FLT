/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedWholeCubicComparison
public import FLT.Mazur.WeierstrassSplitNodalOneGonNode
public import FLT.Mazur.PolygonClosedCubicNodeFiber

/-!
# The actual node and its scheme structure under the whole-cubic comparison

The original residue origin evaluation is [0:0:1]. The complete cubic's
specified node maps to exactly that origin, with equality of the full
ideal sheaves and of the geometric contraction's pulled-back node ideal.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hd : 0 < depth)
local notation "F" => ResidueField R
local notation "V" => W.map (algebraMap R F)

/-- Evaluate the original residue affine chart at its actual nodal origin. -/
def residueNodalOriginEval : Coordinate V 2 →ₐ[F] F :=
  (splitNodalOriginEval (WeierstrassDilatation.residueTangentUnit D)).comp
    (equationChartEquiv (splitDepth_residue_equation D hd) 2).toAlgHom

/-- Every original homogeneous coordinate has its specified origin value. -/
theorem residueNodalOriginEval_coord (i : Fin 3) :
    residueNodalOriginEval D hd (coord V 2 i) = ![0, 0, 1] i := by
  simp only [residueNodalOriginEval, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    equationChartEquiv_coord, splitNodalOriginEval_coord]

/-- The actual origin as a section of the entire original residue cubic. -/
def residueNodalOrigin : Spec (.of F) ⟶ integralCurve V :=
  Spec.map (CommRingCat.ofHom (residueNodalOriginEval D hd).toRingHom) ≫ integralCurveChart V 2

/-- The whole residue comparison retains the original nodal origin as a scheme morphism. -/
@[reassoc] theorem residueOneGonIso_node :
    PolygonNodePresentation.bOrigin F ≫ OneGonGluing.node F ≫
      (residueOneGonIso D hd).hom = residueNodalOrigin D hd := by
  rw [residueOneGonIso, Iso.trans_hom, Iso.symm_hom,
    splitNodalOneGonIso_node_assoc, splitNodalOrigin, Category.assoc, equationCurveIso_chart]
  change Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ _
  rw [← Spec.map_comp_assoc]
  rfl

end FLT.Mazur.WeierstrassIntegralChart

namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart PolygonInfinitesimalStages PolygonOneGonContraction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completeClosedFiberInclusion completePointToIntegralCubic
variable {K : Type} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hd : 2 ≤ depth) [NeZero depth]
local notation "F" => ResidueField A
local notation "E" => resolvedCompleteWholeCubicIso A D hd
local notation "J" => closedPointContractionCubicIso F depth hd (0 : Fin depth)

/-- The complete cubic's specified node is exactly the original residue origin. -/
@[reassoc] theorem resolvedCompleteWholeCubicIso_node :
    closedPointCubicNode F depth hd 0 ≫ (E).hom = residueNodalOrigin D D.depth_pos := by
  simp only [closedPointCubicNode, resolvedCompleteWholeCubicIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  change (PolygonPinching.nodeι F 1 0 ≫ OneGonNormalization.nodes F).left ≫ _ = _
  rw [OneGonNormalization.nodeι_nodes]
  exact (Category.assoc _ _ _).trans (residueOneGonIso_node D D.depth_pos)

/-- The full node ideal, without taking radicals, is retained by the original cubic comparison. -/
theorem resolvedCompleteWholeCubicIso_node_ideal :
    (residueNodalOrigin D D.depth_pos).ker.comap (E).hom =
      (closedPointCubicNode F depth hd 0).ker := by
  rw [← resolvedCompleteWholeCubicIso_node A D hd]
  exact ProjectiveLineMarkedCharts.ker_comap_mono _ _

/-- The full geometric contraction into the original residue cubic retains its pinching map. -/
@[reassoc] theorem closedPointToCubic_residue :
    closedPointToCubic F depth hd 0 ≫ (E).hom =
      closedPointContraction F depth hd 0 ≫ (residueOneGonIso D D.depth_pos).hom := by
  rw [← closedPointContractionCubicIso_fac, resolvedCompleteWholeCubicIso,
    Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The original residue origin has the exact geometric contraction fiber scheme structure. -/
theorem closedPointToCubic_residue_node_ideal :
    (residueNodalOrigin D D.depth_pos).ker.comap
        (closedPointToCubic F depth hd 0 ≫ (E).hom) =
      (closedPointCubicNode F depth hd 0).ker.comap (closedPointToCubic F depth hd 0) := by
  rw [Scheme.IdealSheafData.comap_comp, resolvedCompleteWholeCubicIso_node_ideal]

end FLT.Mazur.WeierstrassDividedDepth
