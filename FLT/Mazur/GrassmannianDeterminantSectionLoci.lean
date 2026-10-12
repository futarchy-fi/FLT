/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianDeterminantSchemeSections
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Exact nonvanishing loci of the determinant coordinates

The selected determinant in each chart cuts out exactly the original overlap.
This identifies the nonvanishing locus on every scheme test with the inverse
image of the selected original Grassmannian chart, scheme-theoretically as opens.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
open Approximation
universe u
set_option backward.isDefEq.respectTransparency false
variable {R M ι : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] {d : ℕ}

/-- The original chart pullback identifies its full overlap open with the determinant open. -/
theorem determinantChartSection_basicOpen (i k : AmbientChartIndex R M ι d) :
    ambientGrassmannianChart R M ι d i ⁻¹ᵁ
        (ambientGrassmannianChart R M ι d k).opensRange =
      PrimeSpectrum.basicOpen (determinantChartSection i k) := by
  have hr : (indexedOverlapInclusion i k).opensRange =
      PrimeSpectrum.basicOpen (determinantChartSection i k) :=
    principalOverlapInclusion_range _ _
  rw [← hr]
  ext x
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback
      (ambientGrassmannianChart_isPullback R M ι d i k) x y hy.symm
    exact ⟨z, hz⟩
  · rintro ⟨z, rfl⟩
    refine ⟨indexedChartTransition i k z, ?_⟩
    exact congrArg (fun g ↦ g z) (ambientGrassmannianChart_overlap R M ι d i k)

/-- The determinant function on any test has exactly the original selected-chart locus. -/
theorem determinantTestSection_basicOpen (i k : AmbientChartIndex R M ι d)
    {T : Scheme.{u}} (a : T ⟶ indexedChartScheme i) :
    T.basicOpen (determinantTestSection i k a) =
      (a ≫ ambientGrassmannianChart R M ι d i) ⁻¹ᵁ
        (ambientGrassmannianChart R M ι d k).opensRange := by
  rw [Scheme.Hom.comp_preimage, determinantChartSection_basicOpen]
  have hb := Scheme.Hom.preimage_basicOpen_top a
    ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin d × ι) R))).inv (determinantChartSection i k))
  exact hb.symm.trans (congrArg (fun W : (indexedChartScheme i).Opens ↦ a ⁻¹ᵁ W)
    (AlgebraicGeometry.basicOpen_eq_of_affine
      (R := .of (MvPolynomial (Fin d × ι) R)) (determinantChartSection i k)))

/-- The coordinate determinant locus in its original affine chart is an actual affine open. -/
theorem determinantChartSection_isAffineOpen (i k : AmbientChartIndex R M ι d) :
    IsAffineOpen (ambientGrassmannianChart R M ι d i ⁻¹ᵁ
      (ambientGrassmannianChart R M ι d k).opensRange) := by
  rw [determinantChartSection_basicOpen]
  exact IsAffineOpen.Spec_basicOpen _

end FLT.Mazur.GrassmannianChart
