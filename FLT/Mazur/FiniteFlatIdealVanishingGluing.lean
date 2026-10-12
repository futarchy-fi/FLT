/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFlatIdealVanishingRestriction

/-!
# The original closed charts cover the global vanishing locus

The global ideal sheaf glues precisely the coefficient charts already
constructed on affine base opens. Their immersions form cartesian squares
with the original affine-open maps and jointly cover the global locus.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteFlatIdealVanishing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {D S : Scheme} (g : D ⟶ S) [IsFinite g] [Flat g]
  [LocallyOfFinitePresentation g] (J : D.IdealSheafData) (U : S.affineOpens)

/-- The original coefficient chart embeds in the glued closed locus. -/
def chartToLocus : chart g J U ⟶ locus g J := (idealSheaf g J).subschemeCover.f U

instance chartToLocus_open : IsOpenImmersion (chartToLocus g J U) :=
  inferInstanceAs (IsOpenImmersion ((idealSheaf g J).subschemeCover.f U))

/-- Gluing retains the exact original map of the chart to the base. -/
@[reassoc (attr := simp)] theorem chartToLocus_inclusion :
    chartToLocus g J U ≫ locusInclusion g J = chartInclusion g J U ≫ U.2.fromSpec := by
  exact ((idealSheaf g J).subschemeCover_map_subschemeι U).trans
    ((idealSheaf g J).glueDataObjι_ι U)

/-- The chart covers exactly the part of the locus over its original affine base open. -/
theorem chartToLocus_opensRange :
    (chartToLocus g J U).opensRange = locusInclusion g J ⁻¹ᵁ U.1 :=
  (idealSheaf g J).opensRange_subschemeCover_map U

/-- Every point of the glued locus lies in an original coefficient chart. -/
theorem chartToLocus_covers (x : locus g J) :
    ∃ U : S.affineOpens, ∃ y : chart g J U, chartToLocus g J U y = x :=
  Scheme.Cover.exists_eq (idealSheaf g J).subschemeCover.openCover x

/-- Each original closed chart is the actual pullback of the global closed immersion. -/
theorem chart_isPullback :
    IsPullback (chartInclusion g J U) (chartToLocus g J U)
      U.2.fromSpec (locusInclusion g J) := by
  apply IsOpenImmersion.isPullback
  · exact chartToLocus_inclusion g J U
  · rw [chartToLocus_opensRange, U.2.opensRange_fromSpec]

end FLT.Mazur.FiniteFlatIdealVanishing
