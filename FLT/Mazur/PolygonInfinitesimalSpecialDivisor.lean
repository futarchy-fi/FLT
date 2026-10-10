/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalBoundaryComparison
public import FLT.Mazur.PolygonInfinitesimalStageLine

/-!
# The closed fiber of the actual boundary line

The specified closed polygon inclusion pulls the concrete stage divisor back
to the original unit-one polygon boundary. The canonical ideal comparison
therefore identifies the positive divisor line on that closed fiber.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonInfinitesimal FCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type u) [Field K] (m n : ℕ) (h : 2 ≤ n) [NeZero n]

omit [NeZero n] in
/-- The closed-fiber boundary is the full original unit-one polygon divisor. -/
theorem boundaryIdeal_specialFiberInclusion :
    (boundaryIdeal K m n h).comap (specialFiberInclusion K m n h) =
      PolygonBoundaryDivisor.ideal K n (PolygonCyclicAtlas.normalization K n h) (fun _ ↦ 1) := by
  have hz := markingDivisor_parameterProjection (parameter K m) n h (reduction K m).toRingHom
    0 (reduction_parameter K m) (fun _ ↦ 1)
  simp only [map_one] at hz
  change (boundaryIdeal K m n h).comap (zeroSpecialization K m n h) =
    markingDivisor K 0 n h (fun _ ↦ 1) at hz
  rw [specialFiberInclusion, Scheme.IdealSheafData.comap_comp, hz, markingDivisor_zeroFiberIso]

/-- The original closed polygon boundary remains the actual Cartier ideal. -/
theorem specialBoundary_cartier :
    RelativeEffectiveCartier (PolygonCyclicAtlas.toBase K n h)
      (PolygonBoundaryDivisor.ideal K n (PolygonCyclicAtlas.normalization K n h) (fun _ ↦ 1)) :=
  PolygonBoundaryDivisor.cartier K n _ (by omega) _
    (PolygonCyclicPushout.isPushout K n h (by omega)) _

/-- The nonflat closed coefficient restriction still preserves the invertible ideal module. -/
instance boundaryIdeal_specialFiber_isIso :
    IsIso (idealModulePullbackHom (boundaryIdeal K m n h) (specialFiberInclusion K m n h)) := by
  apply idealModulePullbackHom_isIso_of_cartier _ (boundaryIdeal_cartier K m n h).1
  rw [boundaryIdeal_specialFiberInclusion]
  exact (specialBoundary_cartier K n h).1

/-- The actual stage boundary line restricts to the original polygon boundary line. -/
def boundaryLineSpecialFiberIso :
    (pullback (specialFiberInclusion K m n h)).obj (boundaryLine K m n h) ≅
      divisorLineBundle
        (PolygonBoundaryDivisor.ideal K n (PolygonCyclicAtlas.normalization K n h) (fun _ ↦ 1))
        (specialBoundary_cartier K n h).1 :=
  divisorLinePullbackIsoOfEq _ (boundaryIdeal_cartier K m n h).1
    (specialBoundary_cartier K n h).1 (boundaryIdeal_specialFiberInclusion K m n h)

end FLT.Mazur.PolygonInfinitesimalStages
