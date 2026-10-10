/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonBoundaryClosedLayer
public import FLT.Mazur.PolygonConstantSections
public import FLT.Mazur.PolygonCyclicPushout

/-!
# Lifting the actual closed polygon's constants

The specified pinching computation identifies closed global functions with
base constants. Their original structural lifts give surjectivity of the
degree-zero closed restriction at every infinitesimal order.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Closed polygon global functions are exactly the original base constants. -/
theorem closedPolygon_constantSections :
    HasConstantGlobalSections (PolygonCyclicAtlas.toBase K n h) :=
  PolygonConstantSections.constants K n (by omega)
    (PolygonCyclicAtlas.normalization K n h) (PolygonCyclicAtlas.nodes K n h)
    (PolygonCyclicPushout.isPushout K n h (by omega))

omit [NeZero n] in
/-- Structural coefficients restrict through the specified original coefficient reduction. -/
theorem specialFiber_stageScalars (m : ℕ) (r : Ring K m) :
    (specialFiberInclusion K m n h).appTop (stageScalars K m n h r) =
      structureScalarMap (PolygonCyclicAtlas.toBase K n h) (reduction K m r) := by
  change ((family K m n h).hom.appTop ≫ (specialFiberInclusion K m n h).appTop)
    ((Scheme.ΓSpecIso (.of (Ring K m))).inv r) = _
  rw [← Scheme.Hom.comp_appTop]
  rw [(specialFiberInclusion_isPullback K m n h).w, Scheme.Hom.comp_appTop]
  change (PolygonCyclicAtlas.toBase K n h).appTop
    ((reductionBase K m).appTop ((Scheme.ΓSpecIso (.of (Ring K m))).inv r)) = _
  apply congrArg ((PolygonCyclicAtlas.toBase K n h).appTop)
  exact (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (reduction K m).toRingHom)) r).symm

/-- Every actual closed global function lifts as a structural coefficient of every stage. -/
theorem specialFiber_appTop_surjective (m : ℕ) :
    Function.Surjective (specialFiberInclusion K m n h).appTop := by
  intro s
  obtain ⟨r, hr⟩ := (closedPolygon_constantSections K n h).2 s
  refine ⟨stageScalars K m n h (algebraMap K (Ring K m) r), ?_⟩
  rw [specialFiber_stageScalars, (reduction K m).commutes]
  exact hr

/-- Degree zero of the original line pullback lifts without a positivity bound. -/
theorem boundaryClosedSections_zero_surjective (m : ℕ) :
    Function.Surjective
      ((SectionGradedLinePullback.powerMap (specialFiberInclusion K m n h)
        (boundaryLineSpecialFiberIso K m n h) 0).app ⊤) := by
  intro s
  obtain ⟨t, ht⟩ := specialFiber_appTop_surjective K n h m s
  refine ⟨t, ?_⟩
  exact (SectionGradedLinePullback.sectionMap_zero _ _ ⊤ t).trans ht

end FLT.Mazur.PolygonInfinitesimalStages
