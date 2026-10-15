/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedCompleteCubicComparison
public import FLT.Mazur.WeierstrassResidueOneGonIso

/-!
# The complete closed cubic equals the entire original residue cubic

Compose the two proved whole-cubic comparisons through the same pinched
one-gon. The resulting isomorphism extends the previously specified smooth
comparison, including its reciprocal Laurent coordinate and infinity.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completeClosedFiberInclusion completePointToIntegralCubic
variable {K : Type} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hd : 2 ≤ depth) [NeZero depth]
local notation "F" => ResidueField A
local notation "V" => W.map (algebraMap A F)
local notation "c" => Over.hom (closedPointCubicOver F depth hd (0 : Fin depth))
local notation "J" => closedPointContractionCubicIso F depth hd (0 : Fin depth)

/-- The entire original closed cubic is the original residue cubic, including its node. -/
def resolvedCompleteWholeCubicIso :
    (closedPointCubicOver F depth hd (0 : Fin depth)).left ≅ integralCurve V :=
  (J).symm ≪≫ residueOneGonIso D D.depth_pos

/-- The full comparison preserves the original coefficient field. -/
@[reassoc] theorem resolvedCompleteWholeCubicIso_structure :
    (resolvedCompleteWholeCubicIso A D hd).hom ≫ integralCurveStructure V = c := by
  rw [resolvedCompleteWholeCubicIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    residueOneGonIso_structure]
  apply (cancel_epi (J).hom).mp
  rw [Iso.hom_inv_id_assoc, closedPointContractionCubicIso_over]
  rfl

/-- The complete cubic's original Laurent chart is precisely the reciprocal residue chart. -/
@[reassoc] theorem resolvedCompleteWholeCubicIso_torus :
    closedPointCubicSmoothTorus F depth hd 0 ≫ (c).smoothLocus.ι ≫
        (resolvedCompleteWholeCubicIso A D hd).hom =
      (ProjectiveLine.inversion F).hom ≫ (infinityResidueSmoothIso D D.depth_pos).hom ≫
        (integralSmoothOpen V).ι := by
  rw [← Category.assoc, closedPointCubicSmoothTorus_inclusion,
    closedPointCubicTorus, resolvedCompleteWholeCubicIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [PolygonAtlas.torus_one, residueOneGonIso_torus]

/-- The new whole-cubic isomorphism extends the already specified entire smooth comparison. -/
@[reassoc] theorem resolvedCompleteWholeCubicIso_smooth :
    (c).smoothLocus.ι ≫ (resolvedCompleteWholeCubicIso A D hd).hom =
      (resolvedCompleteIdentityCubicIso A D hd).hom ≫ (integralSmoothOpen V).ι := by
  apply (cancel_epi (closedPointCubicSmoothTorus F depth hd 0)).mp
  rw [resolvedCompleteWholeCubicIso_torus, resolvedCompleteIdentityCubicIso_torus_assoc]

/-- The actual complete-family infinity section becomes the original residue infinity. -/
@[reassoc] theorem resolvedCompleteWholeCubicIso_marking :
    completePointCubicChangedZero F depth hd (completeClosedBase F) 0 ≫
      (resolvedCompleteWholeCubicIso A D hd).hom = integralCurveZero V := by
  rw [← closedPointContractionCubicIso_marking F depth hd 0,
    resolvedCompleteWholeCubicIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact residueOneGonIso_marking D D.depth_pos 0

end FLT.Mazur.WeierstrassDividedDepth
