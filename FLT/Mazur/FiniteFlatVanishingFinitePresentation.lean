/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveVanishingFinitePresentation
public import FLT.Mazur.FiniteFlatIdealVanishingGluing
public import FLT.Mazur.IdealSheafFiniteEquations

/-!
# Finite presentation of the full finite-flat vanishing locus

Finite equations on the finite family give finite equations on each original
base affine chart. These charts cover the global coefficient locus, proving
local finite presentation of its actual closed immersion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteFlatIdealVanishing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {D S : Scheme} (g : D ⟶ S) [IsFinite g] [Flat g]
  [LocallyOfFinitePresentation g] (J : D.IdealSheafData)

/-- A finitely generated full preimage ideal gives a finitely presented coefficient chart. -/
theorem chartInclusion_locallyOfFinitePresentation (U : S.affineOpens)
    (hJ : (preimageIdeal g J U).FG) :
    LocallyOfFinitePresentation (chartInclusion g J U) := by
  let _ := (g.app U.1).hom.toAlgebra
  let _ : Module.Finite Γ(S, U.1) Γ(D, g ⁻¹ᵁ U.1) := g.finite_app U.1 U.2
  let _ := FCurve.finiteFlat_app_projective g U
  exact ProjectiveIdealVanishing.inclusion_locallyOfFinitePresentation
    Γ(S, U.1) Γ(D, g ⁻¹ᵁ U.1) (preimageIdeal g J U) hJ

/-- Finite equations on each affine preimage suffice for the actual global closed locus. -/
theorem locusInclusion_locallyOfFinitePresentation
    (hJ : ∀ U : S.affineOpens, (preimageIdeal g J U).FG) :
    LocallyOfFinitePresentation (locusInclusion g J) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation)
    (idealSheaf g J).subschemeCover.openCover
  intro U
  change LocallyOfFinitePresentation (chartToLocus g J U ≫ locusInclusion g J)
  rw [chartToLocus_inclusion]
  let _ := chartInclusion_locallyOfFinitePresentation g J U (hJ U)
  infer_instance

/-- Finite presentation of the closed ideal gives finite presentation of its vanishing locus. -/
theorem locusInclusion_of_finitePresentation [LocallyOfFinitePresentation J.subschemeι] :
    LocallyOfFinitePresentation (locusInclusion g J) := by
  apply locusInclusion_locallyOfFinitePresentation g J
  intro U
  exact IdealSheafFiniteEquations.ideal_fg J ⟨g ⁻¹ᵁ U.1, U.2.preimage g⟩

end FLT.Mazur.FiniteFlatIdealVanishing
