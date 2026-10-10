/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineOpenCoverTestRecovery
public import FLT.Mazur.SchemeAffineOverlapGluing
/-!
# Recovery of glued overlap maps on arbitrary affine tests

The actual overlap isomorphism restricts to the original local comparison on every
affine test, using the constructed common pullback cover for recovery.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] CrossRefinement.effectiveComparison sheaf
  overlapChartLocalComparison
variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]

/-- The glued overlap comparison recovers the prescribed map on every affine test. -/
theorem baseOverlapComparison_test {A : CommRingCat.{u}} (f : Spec A ⟶ C.baseOverlap C') :
    (pullback f).map (C.baseOverlapComparison C' D).hom =
      C.overlapChartLocalComparison C' D f :=
  AffineOpenCoverCommonRefinement.comparisonIso_test (C.baseOverlapCover C')
    (P := (pullback (Limits.pullback.fst C.base C'.base)).obj (C.sheaf D))
    (Q := (pullback (Limits.pullback.snd C.base C'.base)).obj (C'.sheaf D))
    (fun f ↦ C.overlapChartLocalComparison C' D f)
    (fun f g α w ↦ C.overlapChartLocalComparison_restrict C' D f g α w)
    (fun _ ↦ inferInstance) f

end FLT.Mazur.SchemeAffineDescent.Chart
