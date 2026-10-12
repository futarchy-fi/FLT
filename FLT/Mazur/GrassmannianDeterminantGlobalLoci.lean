/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianDeterminantLine
public import FLT.Mazur.GrassmannianDeterminantSectionLoci
public import FLT.Mazur.CocycleSectionOpenRecovery

/-!
# Global determinant sections recover the original affine charts

The generator open of each actual global determinant section is exactly its
original Grassmannian chart. The proof compares the original coordinates on
all chart opens, including on nonreduced schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.GrassmannianChart
open FCurve FCurve.ModuleSheafUnitCocycle ModuleSheafOpenImageChart
universe u
set_option backward.isDefEq.respectTransparency false
variable {R M ι : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] {d : ℕ}
local notation "G" => ambientGrassmannianScheme R M ι d
local notation "chart" => ambientGrassmannianChart R M ι d
local notation "g" => determinantCocycle (R := R) (M := M) (ι := ι) (d := d)

/-- On any chart subopen the generator open is the original determinant locus. -/
theorem determinantGlobalSection_generator_preimage (i k : AmbientChartIndex R M ι d)
    (U : (G).Opens) (hi : U ≤ (chart i).opensRange) :
    U.ι ⁻¹ᵁ sectionGeneratorOpen (determinantLine R M ι d) (determinantGlobalSection k) =
      U.ι ⁻¹ᵁ (chart k).opensRange := by
  change U.ι ⁻¹ᵁ sectionGeneratorOpen (g).sheaf (determinantGlobalSection k) = _
  rw [(g).sectionGeneratorOpen_coordinate determinantChartOpens_cover
    (determinantGlobalSection k) i U hi,
    determinantGlobalSection_coordinate]
  unfold determinantAmbientSection
  rw [Iso.hom_inv_id_apply]
  change U.toScheme.basicOpen (determinantTestSection i k (coordinate (chart i) U hi)) = _
  rw [determinantTestSection_basicOpen, coordinate_comp]

/-- The actual global section has precisely its original selected affine chart as generator open. -/
theorem determinantGlobalSection_generator (k : AmbientChartIndex R M ι d) :
    sectionGeneratorOpen (determinantLine R M ι d) (determinantGlobalSection k) =
      (chart k).opensRange := by
  apply Opens.ext
  apply Set.ext
  intro x
  obtain ⟨i, y, hy⟩ := ambientGrassmannianChart_cover R M ι d x
  have hx : x ∈ (chart i).opensRange := ⟨y, hy⟩
  exact Iff.of_eq (congrArg (fun V : (chart i).opensRange.toScheme.Opens ↦
    (⟨x, hx⟩ : (chart i).opensRange.toScheme) ∈ V)
      (determinantGlobalSection_generator_preimage i k (chart i).opensRange le_rfl))

/-- Every constructed determinant section has an affine generator open. -/
theorem determinantGlobalSection_generator_isAffine (k : AmbientChartIndex R M ι d) :
    IsAffineOpen (sectionGeneratorOpen (determinantLine R M ι d) (determinantGlobalSection k)) := by
  rw [determinantGlobalSection_generator]
  exact isAffineOpen_opensRange (chart k)

/-- The actual global determinant sections give an affine section cover of the whole scheme. -/
theorem determinantGlobalSection_generator_cover :
    (⨆ k : AmbientChartIndex R M ι d,
      sectionGeneratorOpen (determinantLine R M ι d) (determinantGlobalSection k)) = ⊤ := by
  simp only [determinantGlobalSection_generator]
  exact determinantChartOpens_cover

end FLT.Mazur.GrassmannianChart
