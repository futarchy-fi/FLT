/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticClosedLayer
public import FLT.Mazur.PolygonClosedScalarLifting

/-!
# Lifting the actual closed polygon's constants

The specified pinching computation identifies closed global functions with
base constants. Their original structural lifts give surjectivity of the
degree-zero closed restriction at every infinitesimal order.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

open FCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family

variable (A : Type) [CommRing A] [IsLocalRing A] (π : A)
  (hπ : algebraMap A (IsLocalRing.ResidueField A) π = 0) (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "K" => IsLocalRing.ResidueField A

omit [NeZero n] in
/-- Structural coefficients restrict through the specified original coefficient reduction. -/
theorem residueFiber_stageScalars (m : ℕ) (r : Quotient A π m) :
    (residueFiberInclusion A π hπ m n h).appTop (stageScalars A π m n h r) =
      structureScalarMap (PolygonCyclicAtlas.toBase K n h) (residueMap A π hπ m r) := by
  change ((family A π m n h).hom.appTop ≫ (residueFiberInclusion A π hπ m n h).appTop)
    ((Scheme.ΓSpecIso (.of (Quotient A π m))).inv r) = _
  rw [← Scheme.Hom.comp_appTop]
  rw [(residueFiberInclusion_isPullback A π hπ m n h).w, Scheme.Hom.comp_appTop]
  change (PolygonCyclicAtlas.toBase K n h).appTop
    ((residueBase A π hπ m).appTop ((Scheme.ΓSpecIso (.of (Quotient A π m))).inv r)) = _
  apply congrArg ((PolygonCyclicAtlas.toBase K n h).appTop)
  exact (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (residueMap A π hπ m))) r).symm

/-- Every actual closed global function lifts as a structural coefficient of every stage. -/
theorem residueFiber_appTop_surjective (m : ℕ) :
    Function.Surjective (residueFiberInclusion A π hπ m n h).appTop := by
  intro s
  obtain ⟨r, hr⟩ := (PolygonInfinitesimalStages.closedPolygon_constantSections K n h).2 s
  obtain ⟨t, ht⟩ := residueMap_surjective A π hπ m r
  refine ⟨stageScalars A π m n h t, ?_⟩
  rw [residueFiber_stageScalars, ht]
  exact hr

/-- Degree zero of the original line pullback lifts without a positivity bound. -/
theorem boundaryResidueSections_zero_surjective (m : ℕ) :
    Function.Surjective
      ((SectionGradedLinePullback.powerMap (residueFiberInclusion A π hπ m n h)
        (boundaryLineResidueIso A π hπ m n h) 0).app ⊤) := by
  intro s
  obtain ⟨t, ht⟩ := residueFiber_appTop_surjective A π hπ n h m s
  refine ⟨t, ?_⟩
  exact (SectionGradedLinePullback.sectionMap_zero _ _ ⊤ t).trans ht

end FLT.Mazur.PolygonArithmeticStages
