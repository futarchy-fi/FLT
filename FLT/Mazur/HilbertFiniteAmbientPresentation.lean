/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineOpenFiniteQuotientChart
public import FLT.Mazur.AllAffineAmbientCharts
public import FLT.Mazur.HilbertSameAmbientChartIso
public import FLT.Mazur.HilbertBoundedAmbientAtlas

/-!
# Finite coordinates for the literal all-sections Hilbert chart

The finite presentation and the all-sections presentation have the same original
ambient open. Full-family comparison identifies their actual Hilbert schemes.
This transports the bounded finite affine atlas to the literal original chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] {Z : Scheme.{u}} (z : Z ⟶ Spec (.of R))
  [LocallyOfFiniteType z] (d : ℕ) (U : Z.affineOpens)

/-- Full Hilbert parameters in a chosen finite presentation of the actual affine open. -/
abbrev finiteAffineAmbientHilbert : Scheme.{u} :=
  ambientHilbertScheme R (AffineOpenFiniteVars z U) d (affineOpenFiniteRelations z U)

/-- The actual finite-coordinate Hilbert scheme is the original all-sections chart. -/
def finiteAffineAmbientHilbertIso :
    finiteAffineAmbientHilbert z d U ≅ (allAffineAmbientCharts z).hilbert d U :=
  sameAmbientHilbertIso R (AffineOpenFiniteVars z U) Γ(Z, U.val) d
    (affineOpenFiniteRelations z U) (affineOpenRelations z U) z
    (affineOpenFiniteQuotientChart z U) (affineOpenQuotientChart z U)
    (affineOpenFiniteQuotientChart_over z U) (affineOpenQuotientChart_over z U)
    ((affineOpenFiniteQuotientChart_opensRange z U).trans
      (affineOpenQuotientChart_opensRange z U).symm)

/-- The presentation comparison preserves the actual parameter's original base map. -/
theorem finiteAffineAmbientHilbertIso_over :
    (finiteAffineAmbientHilbertIso z d U).hom ≫
        ambientHilbertStructure R Γ(Z, U.val) d (affineOpenRelations z U) =
      ambientHilbertStructure R (AffineOpenFiniteVars z U) d (affineOpenFiniteRelations z U) :=
  sameAmbientHilbertIso_over ..

/-- A finite affine atlas on the literal original all-sections chart. -/
def allSectionsBoundedHilbertCover : ((allAffineAmbientCharts z).hilbert d U).OpenCover :=
  (boundedAmbientHilbertCover R (AffineOpenFiniteVars z U) d
    (affineOpenFiniteRelations z U)).pushforwardIso (finiteAffineAmbientHilbertIso z d U).hom

instance : Finite (allSectionsBoundedHilbertCover z d U).I₀ :=
  inferInstanceAs (Finite (Fin d → BoundedHilbertMonomials (AffineOpenFiniteVars z U) d))

instance (m : (allSectionsBoundedHilbertCover z d U).I₀) :
    IsAffine ((allSectionsBoundedHilbertCover z d U).X m) :=
  inferInstanceAs (IsAffine ((boundedAmbientHilbertCover R (AffineOpenFiniteVars z U) d
    (affineOpenFiniteRelations z U)).X m))

/-- Local finite type suffices for quasi-compactness of the original actual Hilbert chart. -/
instance allSectionsAmbientHilbert_compactSpace :
    CompactSpace ((allAffineAmbientCharts z).hilbert d U) :=
  (allSectionsBoundedHilbertCover z d U).compactSpace

end FLT.Mazur.HilbertChart
