/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineFppfChart

/-!
# Covering families of affine fppf descent charts

Apply finite affine refinement over every member of the canonical affine
open cover. The resulting base charts cover the original scheme and retain
the exact canonical open maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeAffineDescent
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (p : Y ⟶ X)
variable [Flat p] [Surjective p] [LocallyOfFinitePresentation p]

/-- Actual faithfully flat descent charts indexed by the canonical affine cover. -/
def fppfCharts (i : X.affineOpenCover.I₀) : Chart p :=
  fppfChart p (X.affineOpenCover.f i)

/-- The base maps are the original canonical affine open-cover maps. -/
@[simp]
lemma fppfCharts_base (i : X.affineOpenCover.I₀) :
    (fppfCharts p i).base = X.affineOpenCover.f i := rfl

instance fppfCharts_base_isOpenImmersion (i : X.affineOpenCover.I₀) :
    IsOpenImmersion (fppfCharts p i).base := by
  rw [fppfCharts_base]
  infer_instance

instance fppfCharts_cover_flat (i : X.affineOpenCover.I₀) :
    Flat (fppfCharts p i).cover := fppfChart_cover_flat p _

instance fppfCharts_cover_locallyOfFinitePresentation (i : X.affineOpenCover.I₀) :
    LocallyOfFinitePresentation (fppfCharts p i).cover :=
  fppfChart_cover_locallyOfFinitePresentation p _

/-- The constructed affine descent charts cover the entire base scheme. -/
theorem fppfCharts_covers : iSup (fun i ↦ (fppfCharts p i).base.opensRange) = ⊤ :=
  X.affineOpenCover.openCover.iSup_opensRange

end FLT.Mazur.SchemeAffineDescent
