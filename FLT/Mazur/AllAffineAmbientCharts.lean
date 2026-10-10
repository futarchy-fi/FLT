/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineOpenQuotientPresentation

/-!
# The Hilbert atlas of all actual affine ambient opens

This atlas is constructed from the original scheme and structure morphism.
Every affine open occurs with its exact image and a proved polynomial
quotient presentation, with no finiteness assumptions on its variables.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} (z : Z ⟶ Spec (.of R))

/-- The actual quotient atlas indexed by all affine opens of the ambient. -/
def allAffineAmbientCharts : AmbientQuotientCharts R z where
  Index := Z.affineOpens
  Vars U := Γ(Z, U.val)
  relations U := affineOpenRelations z U
  chart U := affineOpenQuotientChart z U
  chart_open _U := inferInstance
  chart_over U := affineOpenQuotientChart_over z U

/-- Each original affine open is exactly the image of its constructed quotient chart. -/
theorem allAffineAmbientCharts_opensRange (U : Z.affineOpens) :
    ((allAffineAmbientCharts z).chart U).opensRange = U.val :=
  affineOpenQuotientChart_opensRange z U

/-- The constructed quotient charts cover the original ambient scheme. -/
theorem allAffineAmbientCharts_cover (x : Z) :
    ∃ U : (allAffineAmbientCharts z).Index,
      x ∈ ((allAffineAmbientCharts z).chart U).opensRange := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : Z.Opens) from trivial)
  exact ⟨⟨U, hU⟩, (allAffineAmbientCharts_opensRange z ⟨U, hU⟩).symm ▸ hxU⟩

end FLT.Mazur.HilbertChart
