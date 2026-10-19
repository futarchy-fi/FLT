/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicPrincipalComparison
public import FLT.Mazur.LocallyRingedOpenPullback

/-!
# Cartesian principal affine comparison squares

The actual principal orbit restriction is the pullback of the actual affine
principal open along the canonical comparison, as locally ringed spaces.
This uses the proved comparison square and its exact inverse-image formula.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (W : Opens (Orbit n))
  (s : (invariantSheaf n).obj.obj (op W))

/-- Principal affine comparisons form an actual locally ringed pullback square. -/
theorem invariantAffineComparison_principal_isPullback :
    IsPullback (invariantAffineComparison n (invariantPrincipal n W s))
      (invariantOpenInclusion n (invariantPrincipal_le n W s))
      (invariantAffinePrincipalMap n W s).toLRSHom (invariantAffineComparison n W) :=
  LocallyRingedOpenImage.isPullback_of_range _ _ _ _
    (invariantAffineComparison_principal n W s).symm
    (invariantOpenInclusion_principal_range n W s)

end FLT.Mazur.CyclicCharacteristicOrbit
