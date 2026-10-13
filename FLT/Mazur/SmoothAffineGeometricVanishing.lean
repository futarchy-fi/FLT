/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothGeometricAcyclicHigherImage
public import FLT.Mazur.ProperLinePushforwardTilde
public import FLT.Mazur.AffineCohomologyVanishingAffine

/-!
# Positive cohomology vanishing on arbitrary affine smooth bases

The actual higher-image vanishing and affine quasi-coherent cohomology compute
positive cohomology of the original line, without Noetherian hypotheses.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.LineSectionBaseChange
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X S : Scheme.{0}} [IsAffine S] (f : X ⟶ S) [IsProper f] [Smooth f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ s : S, ∀ n, Subsingleton (ModuleH ((pullback (f.fiberι s)).obj L) (n + 1)))

include hL hV in
/-- Positive cohomology of the original line vanishes over every affine smooth base. -/
theorem smoothAffine_geometricAcyclic_positive_vanishing (n : ℕ) :
    Subsingleton (ModuleH L (n + 1)) := by
  let _ := hL.isFinitePresentation
  let _ := properPushforward_isQuasicoherent f L
  apply (acyclicPushforward_moduleH_subsingleton_iff f L
    (smooth_geometricAcyclic_higherImage f L hL hV) (n + 1)).mp
  exact affine_moduleH_succ_subsingleton _ n

end FLT.Mazur.LineSectionBaseChange
