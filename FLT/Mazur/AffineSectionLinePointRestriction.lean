/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSectionLineChartRestriction
public import FLT.Mazur.FiniteFreeChartPointCompatibility

/-!
# Actual point restriction squares give equal overlap subobjects

On a common affine refinement, genuine dual point compatibility identifies
the original restricted line inclusions. The compatibility hypothesis is
an equality of scheme morphisms, not a supplied equality of subobjects.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.FiniteFreeChartTransitions
open AffineFreeSheafCoordinates NormalizedSectionLine FiniteFreeContragredient ProjectiveSpace
open ModuleSheafMorphismGluing CoherentSubmoduleGluing
variable {X : Scheme.{u}} (M : X.Modules)
variable {U V W : X.Opens} [IsAffine U.toScheme] [IsAffine V.toScheme]
variable [IsAffine W.toScheme] (hU : W ≤ U) (hV : W ≤ V)
variable {ι κ : Type u} [Finite ι] [Finite κ]
variable (e : M.restrict U.ι ≅ SheafOfModules.free ι)
variable (d : M.restrict V.ι ≅ SheafOfModules.free κ)

/-- Genuine restricted chart points identify the original slice subobjects. -/
lemma sectionLine_pointRestriction_subobject (i : ι) (j k : κ)
    (L : Chart Γ(U.toScheme, ⊤) ι i) (N : Chart Γ(V.toScheme, ⊤) κ k)
    (a : Γ(W.toScheme, ⊤)ˣ)
    (ha : functionCoordinates (coordinates W.toScheme (transition M hU hV e d))
      (generator Γ(W.toScheme, ⊤) ι i (baseChange (X.homOfLE hU).appTop.hom i L)) j = a)
    (hp : sectionLinePoint Γ(W.toScheme, ⊤) ι (.id _) i
        (baseChange (X.homOfLE hU).appTop.hom i L) ≫
          (dualProjectiveTransition M hU hV e d).hom =
      sectionLinePoint Γ(W.toScheme, ⊤) κ (.id _) k
        (baseChange (X.homOfLE hV).appTop.hom k N)) :
    Subobject.mk (restrictionEquiv W
      (inclusionOn M (chartSectionLineInclusion M le_rfl e i L) hU)) =
    Subobject.mk (restrictionEquiv W
      (inclusionOn M (chartSectionLineInclusion M le_rfl d k N) hV)) := by
  rw [sectionLine_slice_subobject, sectionLine_slice_subobject]
  exact chartPoint_subobject_eq M hU hV e d i j k _ _ a ha hp

end FLT.Mazur.FiniteFreeChartTransitions
