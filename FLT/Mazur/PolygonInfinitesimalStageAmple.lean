/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteSurjectiveAmpleDescent
public import FLT.Mazur.PolygonInfinitesimalSpecialDivisor
public import FLT.Mazur.RelativeAmpleSectionComparison
public import FLT.Mazur.AmpleAffineBase

/-!
# Ample boundary lines on every actual infinitesimal smoothing stage

The original polygon boundary has its proved cubic projective embedding. The
closed-fiber line comparison and finite-surjective descent of ampleness then
prove ampleness on every entire nonreduced smoothing stage.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K] (m n : ℕ) (h : 2 ≤ n)

/-- The original boundary line is ample by its explicit cubic projective presentation. -/
theorem specialBoundaryLine_ample [NeZero n] :
    AmpleLineBundle
      (divisorLineBundle
        (PolygonBoundaryDivisor.ideal K n (PolygonCyclicAtlas.normalization K n h) (fun _ ↦ 1))
        (specialBoundary_cartier K n h).1) := by
  have hc := PolygonCubicSections.divisor_tensorCube_relativeVeryAmple K n (by omega)
    (PolygonCyclicAtlas.normalization K n h) (PolygonCyclicAtlas.nodes K n h)
    (PolygonCyclicPushout.isPushout K n h (by omega)) (fun _ ↦ 1)
  have ha := RelativeAmple.of_power (by decide : 0 < 3) hc
  exact (ha.relativelyAmpleLineBundle
    (specialBoundary_cartier K n h).1.divisorLineBundle_locallyFreeRankOne).ample_of_affine

/-- The actual boundary line is ample on the whole finite-order smoothing stage. -/
theorem boundaryLine_ample : AmpleLineBundle (boundaryLine K m n h) := by
  let _ : NeZero n := ⟨by omega⟩
  apply ampleLineBundle_of_finiteSurjective (family K m n h).hom
    (specialFiberInclusion K m n h) (boundaryLine_rankOne K m n h)
  exact (specialBoundaryLine_ample K n h).of_iso (boundaryLineSpecialFiberIso K m n h)

/-- These actual ample lines are relatively ample over their truncated coefficient bases. -/
theorem boundaryLine_relativelyAmple :
    RelativelyAmpleLineBundle (family K m n h).hom (boundaryLine K m n h) :=
  (boundaryLine_ample K m n h).relative_of_affine _

end FLT.Mazur.PolygonInfinitesimalStages
