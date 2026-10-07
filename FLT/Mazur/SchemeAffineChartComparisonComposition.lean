/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineChartReconstruction
public import FLT.Mazur.AffineNamedRefinementCompositionRecognition

/-!
# Composition of effective affine chart comparisons

The constructed comparisons respect successive geometric refinements. The proof
uses the named reconstruction composition and faithfully flat uniqueness.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C C' C'' : Chart p)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable (ρ : C.Refinement C') (σ : C'.Refinement C'')

/-- The base pullback composition chart for two geometric refinements. -/
def compositionPullback :
    (pullback (Spec.map σ.base)).obj ((pullback (Spec.map ρ.base)).obj (C.sheaf D)) ≅
      (pullback (Spec.map (ρ.comp σ).base)).obj (C.sheaf D) :=
  AffineRefinementPullback.compositionChart ρ.base σ.base (C.sheaf D)

/-- Named reconstruction charts respect successive geometric refinements. -/
theorem refinementReconstruction_composition :
    (AffineNamedRefinementReconstruction.chart C'.ringMap C''.ringMap σ.base σ.cover
        σ.square C'.cover C''.cover σ.cover_over
        (C.refinementReconstruction C' D ρ)).hom =
      (pullback (Spec.map C''.ringMap)).map (C.compositionPullback C' C'' D ρ σ).hom ≫
        (C.refinementReconstruction C'' D (ρ.comp σ)).hom :=
  AffineNamedRefinementReconstruction.chart_composition_of_eq
    C.ringMap C'.ringMap C''.ringMap
    ρ.base ρ.cover σ.base σ.cover ρ.square σ.square C.cover C'.cover C''.cover
    ρ.cover_over σ.cover_over (C.reconstruction D)
    (C.refinementReconstruction C' D ρ) rfl (C.compositionPullback C' C'' D ρ σ) rfl
    (C.refinementReconstruction C'' D (ρ.comp σ)) rfl

variable [((pullback C'.cover).obj M).IsQuasicoherent]
variable [((pullback C''.cover).obj M).IsQuasicoherent]

attribute [local irreducible] sheaf reconstruction comparison refinementReconstruction
attribute [local irreducible] compositionPullback AffineNamedRefinementReconstruction.chart

/-- Reconstructing successive effective comparisons gives the composite reconstruction. -/
theorem comparison_successive_reconstruction :
    (pullback (Spec.map C''.ringMap)).map
        ((pullback (Spec.map σ.base)).map (C.comparison C' D ρ).hom ≫
          (C'.comparison C'' D σ).hom) ≫ (C''.reconstruction D).hom =
      (pullback (Spec.map C''.ringMap)).map (C.compositionPullback C' C'' D ρ σ).hom ≫
        (C.refinementReconstruction C'' D (ρ.comp σ)).hom := by
  rw [Functor.map_comp, Category.assoc, C'.comparison_reconstruction C'' D σ]
  have h := AffineNamedRefinementReconstruction.chart_naturality
    C'.ringMap C''.ringMap σ.base σ.cover σ.square C'.cover C''.cover σ.cover_over
    (C.refinementReconstruction C' D ρ) (C'.reconstruction D) (C.comparison C' D ρ).hom
    (C.comparison_reconstruction C' D ρ)
  simpa only [refinementReconstruction, AffineNamedRefinementReconstruction.chart] using
    h.trans (C.refinementReconstruction_composition C' C'' D ρ σ)

/-- Actual effective chart comparisons compose through the base pullback composition chart. -/
theorem comparison_composition :
    (pullback (Spec.map σ.base)).map (C.comparison C' D ρ).hom ≫
        (C'.comparison C'' D σ).hom =
      (C.compositionPullback C' C'' D ρ σ).hom ≫ (C.comparison C'' D (ρ.comp σ)).hom := by
  let _ := AffineModulePullbackSections.isQuasicoherent_pullback ρ.base (C.sheaf D)
  let _ := AffineModulePullbackSections.isQuasicoherent_pullback σ.base
    ((pullback (Spec.map ρ.base)).obj (C.sheaf D))
  apply AffineQuasicoherentPullbackFaithful.reconstruction_unique C''.ringMap
    C''.faithfullyFlat (C''.reconstruction D)
  rw [C.comparison_successive_reconstruction C' C'' D ρ σ, Functor.map_comp,
    Category.assoc, C.comparison_reconstruction C'' D (ρ.comp σ)]

end FLT.Mazur.SchemeAffineDescent.Chart
