/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeChartGeneratorRestriction
public import FLT.Mazur.SplitLinePrincipalPoints

/-!
# Constructed unit-coordinate refinements of transported lines

The coordinate retraction of a normalized generator transports through the
actual free chart transition. Its principal coordinate opens cover the
common affine chart, and their images in the base carry actual unit coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.FiniteFreeChartTransitions
open AffineFreeSheafCoordinates NormalizedSectionLine FiniteFreeContragredient
variable {X : Scheme.{u}} (M : X.Modules)
variable {U V W : X.Opens} [IsAffine W.toScheme] (hU : W ≤ U) (hV : W ≤ V)
variable {ι κ : Type u} [Finite ι] [Finite κ]
variable (e : M.restrict U.ι ≅ SheafOfModules.free ι)
variable (d : M.restrict V.ι ≅ SheafOfModules.free κ)

/-- Every overlap point has an affine refinement with an actual transported unit coordinate. -/
lemma exists_unit_refinement (i : ι) (L : Chart Γ(W.toScheme, ⊤) ι i) (x : W.toScheme) :
    ∃ (T : X.Opens) (hT : IsAffine T.toScheme) (h : T ≤ W), W.ι x ∈ T ∧
      let _ := hT
      ∃ (j : κ) (a : Γ(T.toScheme, ⊤)ˣ),
        functionCoordinates (coordinates T.toScheme
            (transition M (h.trans hU) (h.trans hV) e d))
          (generator Γ(T.toScheme, ⊤) ι i
            (baseChange (X.homOfLE h).appTop.hom i L)) j = a := by
  let E := functionCoordinates (coordinates W.toScheme (transition M hU hV e d))
  let v := E (generator Γ(W.toScheme, ⊤) ι i L)
  let r := (LinearMap.proj i).comp E.symm.toLinearMap
  have hr : r v = 1 := by
    dsimp only [r, v, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.symm_apply_apply]
    exact generator_coordinate _ _ i L
  obtain ⟨j, hx⟩ := Opens.mem_iSup.mp
    (show x ∈ ⨆ j, W.toScheme.basicOpen (v j) by
      rw [SplitLinePrincipalPoints.cover v r hr]; trivial)
  let P := W.toScheme.basicOpen (v j)
  let T := W.ι ''ᵁ P
  have hP : IsAffine P.toScheme := inferInstance
  have hT : IsAffine T.toScheme :=
    (show IsAffineOpen P from hP).image_of_isOpenImmersion W.ι
  let _ := hT
  let f := (W.ι.isoImage P).inv
  have hf : f ≫ P.ι = X.homOfLE (W.ι_image_le P) := Scheme.Opens.isoImage_ι_inv_ι W P
  have hu : IsUnit ((X.homOfLE (W.ι_image_le P)).appTop (v j)) := by
    have hv := (SplitLinePrincipalPoints.coordinate_isUnit v j P le_rfl).map f.appTop.hom
    change IsUnit ((f ≫ P.ι).appTop (v j)) at hv
    rwa [hf] at hv
  refine ⟨T, hT, W.ι_image_le P, ⟨x, hx, rfl⟩, j, hu.unit, ?_⟩
  rw [transportedGenerator_restrict]
  exact hu.unit_spec.symm

end FLT.Mazur.FiniteFreeChartTransitions
