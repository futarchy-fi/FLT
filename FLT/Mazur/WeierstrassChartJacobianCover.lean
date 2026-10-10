/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartJacobian
public import FLT.Mazur.WeierstrassChartSchemeGluingData
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances

/-!
# The free-coordinate Jacobian cover

When the discriminant is a unit, the two free-coordinate partial derivatives
generate the unit ideal in each chart. The proof checks every residue field,
so it covers all scheme points and allows arbitrary nonreduced base rings.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ) (j : Fin 3)

include hΔ

/-- At each prime some derivative in a free coordinate is invertible in its residue field. -/
theorem chartPartial_exists_not_mem (p : PrimeSpectrum (Coordinate W j)) :
    ∃ i : Fin 3, i ≠ j ∧ chartPartial W j i ∉ p.asIdeal := by
  let f : Coordinate W j →ₐ[R] p.asIdeal.ResidueField :=
    IsScalarTower.toAlgHom R (Coordinate W j) p.asIdeal.ResidueField
  have hd : (W.map (algebraMap R p.asIdeal.ResidueField)).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ]
    exact (hΔ.map (algebraMap R p.asIdeal.ResidueField)).ne_zero
  have hn := normalized_equation_nonsingular (W.map (algebraMap R p.asIdeal.ResidueField))
    hd j (f ∘ coord W j) (projective_equation_of_hom W j f) (by simp)
  obtain ⟨i, hij, hi⟩ := normalized_free_partial_exists _ j _ hn
    (by simp)
  refine ⟨i, hij, ?_⟩
  intro hm
  apply hi
  rw [← chartPartial_map W j i f]
  exact Ideal.algebraMap_residueField_eq_zero.mpr hm

/-- The free-coordinate principal opens cover the entire chart spectrum. -/
theorem chartPartial_basicOpen_cover :
    (⨆ i : {i : Fin 3 // i ≠ j}, PrimeSpectrum.basicOpen (chartPartial W j i)) = ⊤ := by
  apply TopologicalSpace.Opens.ext
  ext p
  simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion,
    TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  obtain ⟨i, hij, hi⟩ := chartPartial_exists_not_mem W hΔ j p
  exact ⟨⟨i, hij⟩, hi⟩

/-- The actual derivatives generate the unit ideal, not merely a radical ideal. -/
theorem chartPartial_span_eq_top :
    Ideal.span (Set.range (fun i : {i : Fin 3 // i ≠ j} => chartPartial W j i)) = ⊤ :=
  PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp (chartPartial_basicOpen_cover W hΔ j)

/-- The derivative cover as an actual open cover by localization spectra. -/
def chartPartialCover : (chartScheme W j).OpenCover where
  I₀ := {i : Fin 3 // i ≠ j}
  X i := Spec (.of (Localization.Away (chartPartial W j i)))
  f i := PrincipalAffineRefinement.inclusion (chartPartial W j i)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun _ => inferInstance⟩
    intro p
    obtain ⟨i, hij, hi⟩ := chartPartial_exists_not_mem W hΔ j p
    refine ⟨⟨i, hij⟩, ?_⟩
    rw [PrincipalAffineRefinement.range_inclusion]
    exact hi

end FLT.Mazur.WeierstrassIntegralChart
