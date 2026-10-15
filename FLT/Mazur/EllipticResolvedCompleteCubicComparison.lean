/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedCompleteFiberComparison
public import FLT.Mazur.PolygonClosedCubicTorusSmoothIso

/-!
# The two original identity contractions in their closed smooth cubics

The complete family's original closed cubic and the arithmetic residue
cubic have compatible full Laurent coordinates. Reciprocal orientation
makes their comparison agree with the actual arithmetic identity chart.
Both original contractions and coefficient maps are kept in the statements.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completeClosedFiberInclusion completePointToIntegralCubic
attribute [local instance] exactVeroneseProjToBase_lfp
variable {K : Type} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hd : 2 ≤ depth) [NeZero depth]
local notation "F" => ResidueField A
local notation "V" => W.map (algebraMap A F)
local notation "c" => Over.hom (closedPointCubicOver F depth hd (0 : Fin depth))
local notation "pC" => exactVeroneseProjToBase F depth hd
local notation "pA" => resolvedSplitStructure A D
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D
local notation "data" => splitResolutionData A D
local notation "qA" => Spec.map (CommRingCat.ofHom (algebraMap A F))
local notation "fA" => finiteGlobalStructure hπ data (depth / 2) (le_refl _)

/-- The original smooth closed cubics compared in the common reciprocal Laurent coordinate. -/
def resolvedCompleteIdentityCubicIso :
    (c).smoothLocus.toScheme ≅ (integralSmoothOpen V).toScheme :=
  (closedPointCubicSmoothTorusIso F depth hd 0).symm ≪≫ ProjectiveLine.inversion F ≪≫
    infinityResidueSmoothIso D D.depth_pos

/-- The complete closed Laurent parameter becomes exactly the reciprocal arithmetic parameter. -/
@[reassoc] theorem resolvedCompleteIdentityCubicIso_torus :
    closedPointCubicSmoothTorus F depth hd 0 ≫
        (resolvedCompleteIdentityCubicIso A D hd).hom =
      (ProjectiveLine.inversion F).hom ≫ (infinityResidueSmoothIso D D.depth_pos).hom := by
  change (closedPointCubicSmoothTorusIso F depth hd 0).hom ≫
    ((closedPointCubicSmoothTorusIso F depth hd 0).inv ≫ _) = _
  rw [Iso.hom_inv_id_assoc, Iso.trans_hom]

/-- The full cubic comparison is over the original residue field. -/
@[reassoc] theorem resolvedCompleteIdentityCubicIso_structure :
    (resolvedCompleteIdentityCubicIso A D hd).hom ≫ integralSmoothStructure V =
      (c).smoothLocus.ι ≫ c := by
  apply (cancel_epi (closedPointCubicSmoothTorus F depth hd 0)).mp
  rw [resolvedCompleteIdentityCubicIso_torus_assoc,
    infinityResidueSmoothIso_structure, closedPointCubicSmoothTorus_structure,
    ← PolygonSplitGroup.reciprocalGroupIso_left]
  exact (PolygonSplitGroup.reciprocalGroupIso F).hom.hom.hom.hom.w

/-- The two original identity contractions agree after the smooth-cubic comparison. -/
@[reassoc] theorem resolvedCompleteIdentityCubicIso_contraction :
    closedPointCubicSmoothTorus F depth hd 0 ≫
        (resolvedCompleteIdentityCubicIso A D hd).hom ≫ (integralSmoothOpen V).ι ≫
          integralCoefficientMorphism W =
      resolvedReciprocalIdentitySmoothChart A D ≫ (pA).smoothLocus.ι ≫ pullback.snd qA fA ≫
        finiteGlobalContraction hπ data (depth / 2) (le_refl _) := by
  rw [resolvedCompleteIdentityCubicIso_torus_assoc,
    infinityResidueSmoothIso_contraction,
    resolvedReciprocalIdentitySmoothChart_inclusion_assoc,
    resolvedIdentityChart_contraction]

/-- The full atlas comparison also retains the original complete family's identity contraction. -/
@[reassoc] theorem resolvedCompleteSmoothFiberIso_identity_contraction (r : (ResidueField A)ˣ) :
    resolvedReciprocalIdentitySmoothChart A D ≫ (resolvedCompleteSmoothFiberIso A D r hd).hom ≫
        pullback.fst _ _ ≫ (pC).smoothLocus.ι ≫ completePointToIntegralCubic F depth hd 0 =
      closedPointCubicSmoothTorus F depth hd 0 ≫ (c).smoothLocus.ι ≫
        completePointCubicClosedInclusion F depth hd 0 := by
  rw [resolvedCompleteSmoothFiberIso_identity_assoc, completeIdentityChart_inclusion_assoc,
    completeRotation_zero, Category.id_comp, completePointIdentityClosedTorus_inclusion_assoc]
  have H := completePointToCubicBaseChange_fst F depth hd (completeClosedBase F)
    (completeClosedFiberInclusion F depth hd) (PolygonCyclicAtlas.toBase F depth hd)
    (completeClosedFiber_isPullback F depth hd) (0 : Fin depth)
  change closedPointToCubic F depth hd 0 ≫ completePointCubicClosedInclusion F depth hd 0 =
    completeClosedFiberInclusion F depth hd ≫ completePointToIntegralCubic F depth hd 0 at H
  rw [← H, closedPointCubicSmoothTorus_contraction_assoc]

end FLT.Mazur.WeierstrassDividedDepth
