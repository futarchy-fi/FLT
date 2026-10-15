/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonCompleteClosedSmoothSquare
public import FLT.Mazur.PolygonCompleteIdentityChartOperations

/-!
# Closed Laurent coordinates in the original complete identity charts

The finite smooth-polygon atlas is precisely the closed restriction of the
complete identity atlas. The comparison uses the original rotations and
normalization maps, including their original finite labels.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeRotation
  completeClosedFiberInclusion
attribute [local instance] exactVeroneseProjToBase_lfp PolygonPinching.cyclic_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "π" => exactVeroneseProjToBase K n h
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hp" => PolygonCyclicPushout.isPushout K n h (by omega)
local notation "c" => PolygonCyclicAtlas.toBase K n h

omit [NeZero n] in
/-- The original closed polygon structure is locally finitely presented. -/
theorem completeClosedPolygon_lfp :
    LocallyOfFinitePresentation (PolygonCyclicAtlas.polygon K n h).hom :=
  PolygonPinching.cyclic_lfp K n h

attribute [local instance] completeClosedPolygon_lfp

/-- The closed Laurent component with its original finite label. -/
def completeClosedFiniteChart (i : Fin n) :
    Spec (.of (LaurentPolynomial K)) ⟶ (c).smoothLocus.toScheme :=
  smoothFiniteChart K n (by omega) p q hp i

/-- The closed chart retains the actual original normalization inclusion. -/
@[reassoc] theorem completeClosedFiniteChart_inclusion (i : Fin n) :
    completeClosedFiniteChart K n h i ≫ (c).smoothLocus.ι =
      (torusToComponent K ≫ componentι K n i ≫ p).left :=
  smoothFiniteChart_inclusion K n (by omega) p q hp i

/-- Restricting the actual translated identity chart gives its original closed Laurent chart. -/
@[reassoc] theorem completeClosedFiniteChart_identityChart (i : Fin n) (a : ZMod n) :
    completeClosedFiniteChart K n h (rotateIndex a i) ≫
        completeClosedSmoothInclusion K n h =
      completePointIdentityClosedTorus K n h i ≫ (completeIdentityChart K n h i a).left := by
  apply (cancel_mono (π).smoothLocus.ι).mp
  rw [Category.assoc, completeClosedSmoothInclusion_inclusion,
    completeClosedFiniteChart_inclusion_assoc, Category.assoc,
    completeIdentityChart_inclusion, completePointIdentityClosedTorus_inclusion_assoc,
    completeClosedTorus_rotation]

/-- With identity label zero, the chart rotation parameter is exactly the finite label. -/
@[reassoc] theorem completeClosedFiniteChart_zeroIdentityChart (i : Fin n) :
    completeClosedFiniteChart K n h i ≫ completeClosedSmoothInclusion K n h =
      completePointIdentityClosedTorus K n h (0 : Fin n) ≫
        (completeIdentityChart K n h 0 (ZMod.finEquiv n i)).left := by
  have hi : rotateIndex (ZMod.finEquiv n i) (0 : Fin n) = i := by
    simp only [rotateIndex, map_zero, zero_add, RingEquiv.symm_apply_apply]
  simpa only [hi] using
    completeClosedFiniteChart_identityChart K n h (0 : Fin n) (ZMod.finEquiv n i)

end FLT.Mazur.PolygonInfinitesimalStages
