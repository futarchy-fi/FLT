/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertParameterFiniteType
public import FLT.Mazur.HilbertFiniteAmbientPresentation
public import FLT.Mazur.AmpleHilbertFunctorRepresentation
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finite type on the original all-sections Hilbert scheme

Transport finite-coordinate geometry through the proved full-family comparison,
then use the original ambient open cover. This keeps the original glued scheme
and its coefficient-base morphism, rather than replacing the parameter source.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
universe u
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R] {Z : Scheme.{u}} (z : Z ⟶ Spec (.of R))
  [LocallyOfFiniteType z] (d : ℕ)

/-- Every literal all-sections chart has a locally finite type original base map. -/
instance allSectionsHilbertStructure_locallyOfFiniteType (U : Z.affineOpens) :
    LocallyOfFiniteType ((allAffineAmbientCharts z).chartBase d U) := by
  have h : LocallyOfFiniteType ((finiteAffineAmbientHilbertIso z d U).hom ≫
      (allAffineAmbientCharts z).chartBase d U) := by
    change LocallyOfFiniteType ((finiteAffineAmbientHilbertIso z d U).hom ≫
      ambientHilbertStructure R Γ(Z, U.val) d (affineOpenRelations z U))
    rw [finiteAffineAmbientHilbertIso_over]
    infer_instance
  exact (MorphismProperty.cancel_left_of_respectsIso
    (P := @LocallyOfFiniteType) (finiteAffineAmbientHilbertIso z d U).hom _).mp h

/-- The original glued Hilbert parameter is locally of finite type over the original base. -/
instance originalHilbertStructure_locallyOfFiniteType :
    LocallyOfFiniteType ((allAffineAmbientCharts z).gluedBase d) := by
  apply IsZariskiLocalAtSource.of_openCover ((allAffineAmbientCharts z).hilbertOpenCover d)
  intro U
  change LocallyOfFiniteType ((allAffineAmbientCharts z).hilbertChart d U ≫
    (allAffineAmbientCharts z).gluedBase d)
  rw [AmbientQuotientCharts.hilbertChart_over]
  infer_instance

/-- Over a Noetherian coefficient ring, the entire original Hilbert parameter is locally
Noetherian, without assuming finite presentation of a chosen ambient ideal. -/
instance originalHilbert_isLocallyNoetherian [IsNoetherianRing R] :
    IsLocallyNoetherian ((allAffineAmbientCharts z).gluedHilbert d) :=
  LocallyOfFiniteType.isLocallyNoetherian ((allAffineAmbientCharts z).gluedBase d)

end FLT.Mazur.HilbertChart
