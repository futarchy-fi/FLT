/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianDeterminantCocycle
public import FLT.Mazur.CocycleGlobalCoordinates

/-!
# The global Grassmannian determinant line and its sections

The actual determinant cocycle glues a locally free rank-one sheaf. All selected
determinant coordinates glue to global sections, retaining their exact values
on every common subopen of the original charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.GrassmannianChart
open FCurve FCurve.ModuleSheafUnitCocycle
universe u
set_option backward.isDefEq.respectTransparency false
variable {R M ι : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] {d : ℕ}
local notation "G" => ambientGrassmannianScheme R M ι d
local notation "chart" => ambientGrassmannianChart R M ι d
local notation "g" => determinantCocycle (R := R) (M := M) (ι := ι) (d := d)

/-- The original affine chart images cover the whole Grassmannian. -/
theorem determinantChartOpens_cover :
    (⨆ i : AmbientChartIndex R M ι d, (chart i).opensRange) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨i, y, hy⟩ := ambientGrassmannianChart_cover R M ι d x
  exact Opens.mem_iSup.mpr ⟨i, y, hy⟩

variable (R M ι d) in
/-- The actual line sheaf glued from the original determinant coordinates. -/
def determinantLine : (G).Modules := (g).sheaf

/-- The determinant sheaf trivializes on every original chart image. -/
def determinantLineOpenIso (i : AmbientChartIndex R M ι d) :
    (determinantLine R M ι d).restrict (chart i).opensRange.ι ≅
      structureModule (chart i).opensRange.toScheme := (g).restrictIso i

variable (R M ι d) in
/-- Original chart coverage and actual trivializations prove rank one globally. -/
theorem determinantLine_locallyFreeRankOne :
    LocallyFreeRankOne (determinantLine R M ι d) :=
  (g).locallyFreeRankOne determinantChartOpens_cover

/-- A selected determinant gives compatible sections on all original charts. -/
def determinantGlobalSection (k : AmbientChartIndex R M ι d) :
    Γ(determinantLine R M ι d, ⊤) :=
  ⟨fun i ↦ determinantAmbientSection i k (⊤ ⊓ (chart i).opensRange) inf_le_right, by
    intro i j V hi hj
    rw [determinantAmbientSection_refine, determinantAmbientSection_refine]
    exact determinantAmbientSection_transition i j k V
      (hi.trans inf_le_right) (hj.trans inf_le_right)⟩

/-- Every glued section retains its original determinant on every chart subopen. -/
theorem determinantGlobalSection_coordinate (i k : AmbientChartIndex R M ι d)
    (U : (G).Opens) (hi : U ≤ (chart i).opensRange) :
    (g).globalCoordinate (determinantGlobalSection k) i U hi =
      determinantAmbientSection i k U hi :=
  determinantAmbientSection_refine i k _ U (le_inf le_top hi) inf_le_right

/-- The selected section has coordinate one in its own original chart. -/
theorem determinantGlobalSection_self (i : AmbientChartIndex R M ι d)
    (U : (G).Opens) (hi : U ≤ (chart i).opensRange) :
    (g).globalCoordinate (determinantGlobalSection i) i U hi = 1 := by
  rw [determinantGlobalSection_coordinate]
  unfold determinantAmbientSection
  rw [determinantOpenSection_self, map_one]

end FLT.Mazur.GrassmannianChart
