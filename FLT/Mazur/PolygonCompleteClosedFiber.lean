/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOriginalStageAdicSquare
public import FLT.Mazur.PolygonInfinitesimalStageFiber

/-!
# The original polygon as the closed fiber of the complete candidate

Pasting the original closed-stage square with the actual adic realization
identifies the complete candidate's closed fiber, preserving its original maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] family originalStageToCompatibleProj

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The closed coefficient point of the original complete power-series base. -/
def completeClosedBase : Spec (.of K) ⟶ Spec (.of (PowerSeries K)) :=
  Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff : PowerSeries K →+* K))

/-- Reduction through every original coefficient stage is the same closed base point. -/
theorem reductionBase_toSeries (m : ℕ) :
    reductionBase K m ≫ baseToSeries K m = completeClosedBase K := by
  rw [reductionBase, baseToSeries, completeClosedBase, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext f
  exact reduction_seriesToStage K m f

/-- The original polygon's closed inclusion in the actual complete candidate. -/
def completeClosedFiberInclusion : PolygonCyclicAtlas.scheme K n h ⟶ exactVeroneseProj K n h :=
  specialFiberInclusion K 0 n h ≫ originalStageToCompatibleProj K n h 0

/-- The complete candidate has the original cyclic polygon as its cartesian closed fiber. -/
theorem completeClosedFiber_isPullback :
    IsPullback (completeClosedFiberInclusion K n h) (PolygonCyclicAtlas.toBase K n h)
      (exactVeroneseProjToBase K n h) (completeClosedBase K) := by
  have hp := (specialFiberInclusion_isPullback K 0 n h).paste_horiz
    (originalStageToCompatibleProj_isPullback K n h 0)
  rw [reductionBase_toSeries] at hp
  exact hp

/-- The actual closed fiber is isomorphic to the original polygon. -/
def completeClosedFiberIso : PolygonCyclicAtlas.scheme K n h ≅
    pullback (exactVeroneseProjToBase K n h) (completeClosedBase K) :=
  (completeClosedFiber_isPullback K n h).isoPullback

/-- The comparison preserves the original polygon's inclusion in the total scheme. -/
@[reassoc] theorem completeClosedFiberIso_fst :
    (completeClosedFiberIso K n h).hom ≫ pullback.fst _ _ =
      completeClosedFiberInclusion K n h :=
  (completeClosedFiber_isPullback K n h).isoPullback_hom_fst

/-- The comparison preserves the original polygon's structure morphism. -/
@[reassoc] theorem completeClosedFiberIso_snd :
    (completeClosedFiberIso K n h).hom ≫ pullback.snd _ _ =
      PolygonCyclicAtlas.toBase K n h :=
  (completeClosedFiber_isPullback K n h).isoPullback_hom_snd

end FLT.Mazur.PolygonInfinitesimalStages
