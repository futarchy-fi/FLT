/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSplitDepthLaurentPoints

/-!
# The original Laurent contraction realizes the actual residue points

Evaluate the full original infinity chart and retain its homogeneous
coordinates. This identifies its contraction with the classical residue
point morphism, including the inverse-character parametrization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] {A : ValuationSubring K}
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
local notation "F" => ResidueField A
local notation "a" => WeierstrassDilatation.residueTangentUnit D

/-- Evaluate the actual original infinity chart at its Laurent unit. -/
def splitDepthLaurentEvaluation (t : Fˣ) : Coordinate W 1 →ₐ[A] F :=
  ((LaurentUnitPoints.evalUnit (R := F) t).restrictScalars A).comp
    (infinityResidueOriginalMap D D.depth_pos)

/-- The evaluated original coordinates are the same normalized nodal unit coordinates. -/
theorem splitDepthLaurentEvaluation_coord (t : Fˣ) (i : Fin 3) :
    splitDepthLaurentEvaluation D t (coord W 1 i) =
      splitNodalUnitChart a t (coord (splitNodalEquation a) 1 i) := by
  change LaurentUnitPoints.evalUnit t (infinityResidueOriginalMap D D.depth_pos
    (coord W 1 i)) = LaurentUnitPoints.evalUnit t
      (splitNodalChartToLaurent a (coord (splitNodalEquation a) 1 i))
  rw [infinityResidueOriginalMap_coord, splitNodalChartToLaurent_coord]

/-- The original residue point has exactly the evaluated homogeneous coordinates. -/
theorem splitDepthLaurentPoint_evaluation (t : Fˣ) :
    (splitDepthLaurentPoint D t).point =
      (⟦fun i => splitDepthLaurentEvaluation D t (coord W 1 i)⟧ : Projective.PointClass F) := by
  rw [splitDepthLaurentPoint_point]
  change (⟦_⟧ : Projective.PointClass F) = ⟦_⟧
  congr 1
  funext i
  exact (splitDepthLaurentEvaluation_coord D t i).symm

/-- The original Laurent contraction is the actual projective residue point morphism. -/
theorem splitDepthLaurentPoint_contraction (t : Fˣ) :
    Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := F) t).toRingHom) ≫
        infinityResidueContraction D D.depth_pos =
      (projectiveToIntegral W (splitDepthLaurentPoint D t)).left := by
  let f := splitDepthLaurentEvaluation D t
  rw [projectiveToIntegral_chart W (splitDepthLaurentPoint D t) 1
    (fun i => f (coord W 1 i)) (chartAlgHom_equation W 1 f) (by simp)
    (splitDepthLaurentPoint_evaluation D t).symm]
  rw [integralChartPoint, evaluation_chartAlgHom]
  change _ ≫ (Spec.map _ ≫ _) = Spec.map _ ≫ _
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

variable [DecidableEq (ResidueField A)]

/-- Every original smooth residue point is the inverse-character Laurent contraction. -/
theorem splitDepthLaurent_inverse_character_contraction
    (P : (W.map (residue A)).toProjective.Point) :
    Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := F)
      (Additive.toMul (splitDepthResidueCharacter D P.toAffineLift))⁻¹).toRingHom) ≫
        infinityResidueContraction D D.depth_pos = (projectiveToIntegral W P).left := by
  rw [splitDepthLaurentPoint_contraction, splitDepthLaurentPoint_inverse_character]

end FLT.Mazur.WeierstrassIntegralChart
