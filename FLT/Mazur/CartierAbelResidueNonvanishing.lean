/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierAbelDirectImageBaseChange
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# The actual Cartier direct-image map is nonzero in every residue fiber

Surjectivity supplies a point in each actual scheme-theoretic fiber. The
geometric Cartier section then proves nonvanishing of the original map after
pullback to the residue spectrum. Geometrically integral families satisfy
the surjectivity hypothesis through the existing geometric instance.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.CartierAbel
open FCurve
attribute [local irreducible] twistedSectionPushforwardEquiv lineHomSectionEquiv
  moduleSheafDualPullbackIso
variable {X S : Scheme.{0}} (f : X ⟶ S) [Surjective f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)

/-- Every actual residue pullback of a relative Cartier direct-image map is nonzero. -/
theorem relativeSection_residue_directImage_ne_zero
    (s : RelativeSection f L hL) (x : S) :
    (pullback (S.fromSpecResidueField x)).map (s.val.toDirectImage f L).map ≠ 0 := by
  obtain ⟨y, hy⟩ := f.surjective x
  let _ : Nonempty (Limits.pullback f (S.fromSpecResidueField x) : Scheme) :=
    ⟨(f.fiberHomeo x).symm ⟨y, hy⟩⟩
  exact relativeSection_pullback_directImage_ne_zero f (S.fromSpecResidueField x) L hL s

end FLT.Mazur.CartierAbel
