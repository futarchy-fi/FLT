/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteH1Rank
public import FLT.Mazur.FlatSpectrumStructureRank
public import FLT.Mazur.ChowAffineCover

/-!
# Actual generic and geometric generic H1 dimension

Flat affine cohomology base change carries rank one of the original
complete family's H1 to every extension of its actual fraction field.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve Chow.AffineBase

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Any flat field-valued coefficient map gives actual first cohomology of dimension one. -/
theorem completeFlatFieldH1_finrank (L : Type) [Field L]
    (g : Spec (.of L) ⟶ Spec (.of (PowerSeries K))) [Flat g] :
    Module.finrank L (H1 (pullback.snd (exactVeroneseProjToBase K n h) g)) = 1 := by
  classical
  let _ : (exactVeroneseProj K n h).IsSeparated :=
    inferInstanceAs (Proj (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))).IsSeparated
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : CompactSpace (exactVeroneseProj K n h) :=
    QuasiCompact.compactSpace_of_compactSpace (exactVeroneseProjToBase K n h)
  let _ := completeStructureH1_free K n h
  obtain ⟨ι, hι, U, hU, _, hCover⟩ :=
    Chow.exists_finite_nonempty_affine_cover (exactVeroneseProj K n h)
  let _ := hι
  let _ := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  exact (IncreasingCechCartesian.flat_structure_cohomology_finrank
    (IsPullback.of_hasPullback (exactVeroneseProjToBase K n h) g)
    U hU hCover g.flat_appTop 0).trans (completeStructureH1_finrank K n h)

/-- The actual generic fiber has first structure cohomology of dimension one. -/
theorem completeGenericH1_finrank (F : Type) [Field F] [Algebra (PowerSeries K) F]
    [IsFractionRing (PowerSeries K) F] :
    Module.finrank F (H1 (pullback.snd (exactVeroneseProjToBase K n h)
      (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) F))))) = 1 := by
  let _ : Flat (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) F))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  exact completeFlatFieldH1_finrank K n h F _

/-- Every field extension of the actual generic fiber has H1 of dimension one. -/
theorem completeGeometricGenericH1_finrank (F L : Type) [Field F] [Field L]
    [Algebra (PowerSeries K) F] [IsFractionRing (PowerSeries K) F]
    [Algebra F L] [Algebra (PowerSeries K) L] [IsScalarTower (PowerSeries K) F L] :
    Module.finrank L (H1 (pullback.snd (exactVeroneseProjToBase K n h)
      (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) L))))) = 1 := by
  have hf : (algebraMap (PowerSeries K) F).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  have hl : (algebraMap F L).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  let _ : Flat (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) L))) := by
    apply Flat.SpecMap_iff.mpr
    rw [IsScalarTower.algebraMap_eq (PowerSeries K) F L]
    exact hf.comp hl
  exact completeFlatFieldH1_finrank K n h L _

end FLT.Mazur.PolygonInfinitesimalStages
