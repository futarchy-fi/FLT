/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineChartRefinementCategory

/-!
# Reconstruction characterizes affine chart comparisons

The effective comparison reconstructs the original sheaf through the actual
cover factorization. Faithful flatness makes this square determine the map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]
variable (ρ : C.Refinement C')

/-- Reconstruct a restricted chart using its geometric cover factorization. -/
def refinementReconstruction :
    (pullback (Spec.map C'.ringMap)).obj
        ((pullback (Spec.map ρ.base)).obj (C.sheaf D)) ≅ (pullback C'.cover).obj M :=
  AffineRefinementPullback.reconstruction C.ringMap C'.ringMap ρ.base ρ.cover ρ.square
    (C.reconstruction D) ≪≫
      (SheafPullbackPathComparison.comparison (Spec.map ρ.cover) C.cover C'.cover
        ρ.cover_over).app M

/-- Effective comparison has exactly the reconstruction specified by the refinement. -/
@[reassoc]
theorem comparison_reconstruction :
    (pullback (Spec.map C'.ringMap)).map (C.comparison C' D ρ).hom ≫
        (C'.reconstruction D).hom = (C.refinementReconstruction C' D ρ).hom :=
  D.chartRefinementIsoTo_reconstruction C.ringMap C'.ringMap ρ.base ρ.cover ρ.square p
    C.base C.cover C.square C.faithfullyFlat C'.faithfullyFlat C'.base C'.cover
    ρ.base_over ρ.cover_over C'.square

/-- The reconstruction square uniquely specifies the effective chart comparison. -/
theorem comparison_unique
    (f : (pullback (Spec.map ρ.base)).obj (C.sheaf D) ⟶ C'.sheaf D)
    (hf : (pullback (Spec.map C'.ringMap)).map f ≫ (C'.reconstruction D).hom =
      (C.refinementReconstruction C' D ρ).hom) : f = (C.comparison C' D ρ).hom := by
  let _ := AffineModulePullbackSections.isQuasicoherent_pullback ρ.base (C.sheaf D)
  exact AffineQuasicoherentPullbackFaithful.reconstruction_unique C'.ringMap
    C'.faithfullyFlat (C'.reconstruction D) f _
    (hf.trans (C.comparison_reconstruction C' D ρ).symm)

end FLT.Mazur.SchemeAffineDescent.Chart
