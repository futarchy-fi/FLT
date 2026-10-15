/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedPolygonComparison
public import FLT.Mazur.PolygonCompleteClosedChartComparison

/-!
# The arithmetic resolved smooth fiber in the complete polygon family

Over the original residue field, compare the entire arithmetic resolved
smooth fiber with the actual closed fiber of the complete relative smooth
scheme. Its finite charts become the original complete identity charts.
No map from the power-series base to the valuation ring is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonPinching PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local instance] exactVeroneseProjToBase_lfp PolygonPinching.cyclic_lfp
  completeClosedPolygon_lfp
variable {K : Type} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (r : (ResidueField A)ˣ) (hd : 2 ≤ depth) [NeZero depth]
local notation "F" => ResidueField A
local notation "pA" => resolvedSplitStructure A D
local notation "pC" => exactVeroneseProjToBase F depth hd
local notation "p" => PolygonCyclicAtlas.normalization F depth hd
local notation "q" => PolygonCyclicAtlas.nodes F depth hd
local notation "hp" => PolygonCyclicPushout.isPushout F depth hd D.depth_pos
local notation "c" => PolygonCyclicAtlas.toBase F depth hd

/-- The complete family's original closed polygon, with the actual arithmetic coordinates. -/
def resolvedCompletePolygonIso : (pA).smoothLocus.toScheme ≅ (c).smoothLocus.toScheme :=
  resolvedPolygonSmoothIso A D r p q hp

/-- The actual arithmetic smooth fiber is the whole smooth closed fiber of the complete family. -/
def resolvedCompleteSmoothFiberIso : (pA).smoothLocus.toScheme ≅
    pullback ((pC).smoothLocus.ι ≫ pC) (completeClosedBase F) :=
  resolvedCompletePolygonIso A D r hd ≪≫ completeClosedSmoothFiberIso F depth hd

/-- The comparison to the complete family preserves its original closed coefficient map. -/
@[reassoc] theorem resolvedCompleteSmoothFiberIso_snd :
    (resolvedCompleteSmoothFiberIso A D r hd).hom ≫ pullback.snd _ _ =
      (pA).smoothLocus.ι ≫ pA := by
  rw [resolvedCompleteSmoothFiberIso, Iso.trans_hom, Category.assoc,
    completeClosedSmoothFiberIso_snd]
  exact resolvedPolygonSmoothIso_structure A D r p q hp

/-- The original arithmetic component lands in exactly the same original complete identity chart. -/
@[reassoc] theorem resolvedCompleteSmoothFiberIso_chart (i : Fin depth) :
    resolvedOrientedComponentChart A D r i ≫ (resolvedCompleteSmoothFiberIso A D r hd).hom ≫
        pullback.fst _ _ = completePointIdentityClosedTorus F depth hd (0 : Fin depth) ≫
          (completeIdentityChart F depth hd 0 (ZMod.finEquiv depth i)).left := by
  rw [resolvedCompleteSmoothFiberIso, Iso.trans_hom, Category.assoc,
    completeClosedSmoothFiberIso_fst]
  change resolvedOrientedComponentChart A D r i ≫
    (resolvedPolygonSmoothIso A D r p q hp).hom ≫ _ = _
  rw [resolvedPolygonSmoothIso_chart_assoc]
  exact completeClosedFiniteChart_zeroIdentityChart F depth hd i

/-- In particular, the reciprocal arithmetic identity is the original complete zero chart. -/
@[reassoc] theorem resolvedCompleteSmoothFiberIso_identity :
    resolvedReciprocalIdentitySmoothChart A D ≫ (resolvedCompleteSmoothFiberIso A D r hd).hom ≫
        pullback.fst _ _ = completePointIdentityClosedTorus F depth hd (0 : Fin depth) ≫
          (completeIdentityChart F depth hd 0 0).left := by
  rw [← resolvedOrientedComponentChart_zero A D r]
  have h0 : (⟨0, D.depth_pos⟩ : Fin depth) = 0 := Fin.ext rfl
  rw [h0, resolvedCompleteSmoothFiberIso_chart, map_zero]

end FLT.Mazur.WeierstrassDividedDepth
