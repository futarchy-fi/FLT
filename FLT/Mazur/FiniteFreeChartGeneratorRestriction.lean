/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineFreeSectionLineBaseChange
public import FLT.Mazur.FiniteFreeChartProjectiveRestriction

/-!
# Restriction of transported normalized generators

The transported generator on a smaller affine open is obtained by applying
the actual coefficient map to the original transported generator. This
lets principal coordinate neighborhoods supply genuine units after refinement.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.FiniteFreeChartTransitions
open AffineFreeSheafCoordinates NormalizedSectionLine FiniteFreeContragredient
variable {X : Scheme.{u}} (M : X.Modules)
variable {U V W T : X.Opens} [IsAffine W.toScheme] [IsAffine T.toScheme]
variable (hU : W ≤ U) (hV : W ≤ V) (h : T ≤ W)
variable {ι κ : Type u} [Finite ι] [Finite κ]
variable (e : M.restrict U.ι ≅ SheafOfModules.free ι)
variable (d : M.restrict V.ι ≅ SheafOfModules.free κ)

/-- Genuine chart transport of normalized generators commutes with affine refinement. -/
lemma transportedGenerator_restrict (i : ι) (L : Chart Γ(W.toScheme, ⊤) ι i) :
    functionCoordinates (coordinates T.toScheme
        (transition M (h.trans hU) (h.trans hV) e d))
      (generator Γ(T.toScheme, ⊤) ι i (baseChange (X.homOfLE h).appTop.hom i L)) =
    fun j ↦ (X.homOfLE h).appTop
      (functionCoordinates (coordinates W.toScheme (transition M hU hV e d))
        (generator Γ(W.toScheme, ⊤) ι i L) j) := by
  rw [generator_baseChange]
  exact (functionCoordinates_coefficient (X.homOfLE h).appTop.hom _ _
    (transition_coordinates_restrict M hU hV h e d) _).symm

end FLT.Mazur.FiniteFreeChartTransitions
