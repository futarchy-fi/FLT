/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedOddCyclicCoordinates
public import FLT.Mazur.PolygonPinchingAdjustedClosedComparison
public import FLT.Mazur.WeierstrassDividedOddCompleteClosedComparison
public import FLT.Mazur.EllipticResolvedCompleteFiberComparison
import all FLT.Mazur.PolygonPinchingAdjustedClosedComparison
import all FLT.Mazur.WeierstrassDividedZeroCyclePushout

/-!
# The full odd closed comparison extending the original arithmetic smooth atlas

Correct the original projective components by the inverse arithmetic scales.
The resulting isomorphism includes every node and agrees on the entire smooth
fiber with the independently constructed complete smooth comparison.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonPinching PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeClosedFiberInclusion adjustedPinchingCompleteClosedIso
attribute [local instance] exactVeroneseProjToBase_lfp
variable {K : Type} [Field K] (A : ValuationSubring K) (s : ℕ)
  {W : WeierstrassCurve A} {π : A} (D : SplitNodeDepth W π (2 * s + 3))
  (r : (ResidueField A)ˣ)
local notation "F" => ResidueField A
local notation "n" => 2 * s + 3
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D
local notation "data" => splitResolutionData A D
local notation "pA" => resolvedSplitStructure A D
local notation "pC" => exactVeroneseProjToBase F n (by omega)
local notation "N" => zeroSplitCycleNormalization hπ data D s (by omega) rfl
  (by omega) (by omega)
local notation "Q" => zeroSplitCycleNodes hπ data D s (by omega) (by omega) (by omega)
local notation "H" => zeroSplitCycleCocone_isPushout hπ data D s (by omega) rfl (by omega)
local notation "a" => fun i : Fin n => (resolvedCyclicCoordinateScale D r (Fin.val i))⁻¹
local notation "Nc" => PolygonCyclicAtlas.normalization F n (by omega)

/-- Correct every component of the original full odd closed comparison. -/
def resolvedOddAdjustedClosedIso : resolvedSplitFiber A D ≅
    pullback pC (completeClosedBase F) :=
  eqToIso (finiteGlobalTensorModel_index_congr hπ data F (le_refl _) (by omega)
    (show n / 2 = s + 1 by omega)) ≪≫
      adjustedPinchingCompleteClosedIso F n (by omega) N Q H a

/-- Full coordinate adjustment preserves the original arithmetic coefficient map. -/
@[reassoc] theorem resolvedOddAdjustedClosedIso_snd :
    (resolvedOddAdjustedClosedIso A s D r).hom ≫ pullback.snd _ _ = pA := by
  rw [resolvedOddAdjustedClosedIso, Iso.trans_hom, Category.assoc,
    adjustedPinchingCompleteClosedIso_snd]
  exact finiteGlobalTensorModel_structure_transport hπ data F _ _ (by omega)

/-- Every original arithmetic chart has its exact unscaled coordinate after full adjustment. -/
@[reassoc] theorem resolvedOddAdjustedClosedIso_chart (i : Fin n) :
    resolvedOrientedComponentChart A D r i ≫ (pA).smoothLocus.ι ≫
        (resolvedOddAdjustedClosedIso A s D r).hom ≫ pullback.fst _ _ =
      (torusToComponent F).left ≫ (componentι F n i ≫ Nc).left ≫
        completeClosedFiberInclusion F n (by omega) := by
  rw [resolvedOddAdjustedClosedIso, Iso.trans_hom]
  simp only [Category.assoc, eqToIso.hom]
  rw [resolvedOrientedComponentChart_odd_cyclic_assoc A D r s rfl]
  have h := adjustedPinchingCompleteClosedIso_scaledTorus F n (by omega) N Q H a
    i (resolvedCyclicCoordinateScale D r i.val) rfl
  simpa only [zeroSplitCycleNormalization_ι] using h

/-- On the entire arithmetic smooth fiber the adjusted full comparison is W308's comparison. -/
@[reassoc] theorem resolvedOddAdjustedClosedIso_smooth :
    (pA).smoothLocus.ι ≫ (resolvedOddAdjustedClosedIso A s D r).hom ≫ pullback.fst _ _ =
      (resolvedCompleteSmoothFiberIso A D r (by omega)).hom ≫ pullback.fst _ _ ≫
        (pC).smoothLocus.ι := by
  apply (cancel_epi (resolvedOrientedAtlasMap A D r)).mp
  apply Sigma.hom_ext
  intro i
  simp only [resolvedOrientedAtlasMap_chart_assoc,
    resolvedOddAdjustedClosedIso_chart, resolvedCompleteSmoothFiberIso_chart_assoc]
  have h := congrArg (fun f => f ≫ (pC).smoothLocus.ι)
    (completeClosedFiniteChart_zeroIdentityChart F n (by omega) i)
  rw [Category.assoc, completeClosedSmoothInclusion_inclusion,
    completeClosedFiniteChart_inclusion_assoc] at h
  simpa only [Over.comp_left, Category.assoc] using h

end FLT.Mazur.WeierstrassDividedDepth
