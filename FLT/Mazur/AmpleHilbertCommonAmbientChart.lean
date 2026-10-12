/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertChartImage
public import FLT.Mazur.AmpleHilbertFiniteSupport

/-!
# One original ambient Hilbert chart contains finitely many parameters

The full universal family and its exact support opens give a common chart
for every finite set in the glued Hilbert scheme. Pullback gives actual
source neighborhoods, without asserting that an affine ambient has affine Hilbert scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover FLT.Mazur.FCurve
namespace FLT.Mazur.HilbertChart
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {Z : Scheme} (z : Z ⟶ Spec (.of R)) [IsProper z]
  {L : Z.Modules} (hL : AmpleLineBundle L) (d : ℕ)
local notation "A" => allAffineAmbientCharts z

include hL in
/-- Finitely many original Hilbert points lie in one chart for a single affine ambient. -/
theorem exists_common_ambient_hilbert_chart (t : Set ((A).gluedHilbert d)) (ht : t.Finite) :
    ∃ U : (A).Index, t ⊆ ((A).hilbertChart d U).opensRange := by
  obtain ⟨U, hU⟩ := exists_common_affine_support_open z hL d
    ((A).gluedBase d) ((A).universalFamily d) t ht
  change t ⊆ (A).chartSupportLocus d U at hU
  rw [(A).chartSupportLocus_eq] at hU
  exact ⟨U, hU⟩

include hL in
/-- The common chart pulls back to an actual open containing a finite set of source points. -/
theorem exists_common_ambient_chart_preimage {Y : Scheme}
    (g : Y ⟶ (A).gluedHilbert d) (t : Set Y) (ht : t.Finite) :
    ∃ U : (A).Index, t ⊆ g ⁻¹ᵁ ((A).hilbertChart d U).opensRange := by
  obtain ⟨U, hU⟩ := exists_common_ambient_hilbert_chart z hL d (g '' t) (ht.image g)
  exact ⟨U, fun x hx ↦ hU (Set.mem_image_of_mem g hx)⟩

/-- The original source map on the common-chart preimage factors through that chart. -/
def commonAmbientChartLift {Y : Scheme} (g : Y ⟶ (A).gluedHilbert d) (U : (A).Index) :
    (g ⁻¹ᵁ ((A).hilbertChart d U).opensRange).toScheme ⟶ (A).hilbert d U :=
  IsOpenImmersion.lift ((A).hilbertChart d U)
    ((g ⁻¹ᵁ ((A).hilbertChart d U).opensRange).ι ≫ g) (by
      rintro _ ⟨x, rfl⟩
      exact x.property)

omit [IsProper z] in
/-- The factorization retains the original Hilbert parameter, including all nilpotent data. -/
@[reassoc]
theorem commonAmbientChartLift_fac {Y : Scheme} (g : Y ⟶ (A).gluedHilbert d) (U : (A).Index) :
    commonAmbientChartLift z d g U ≫ (A).hilbertChart d U =
      (g ⁻¹ᵁ ((A).hilbertChart d U).opensRange).ι ≫ g :=
  IsOpenImmersion.lift_fac _ _ _

end FLT.Mazur.HilbertChart
