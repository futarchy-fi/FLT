/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundedMonomialCover
public import FLT.Mazur.HilbertPolynomialParameterInverse

/-!
# A finite affine atlas for the actual polynomial Hilbert scheme

Uniformly bounded monomial charts cover every affine parameter through its
actual quotient family. Applying this to the original chart spectra produces
an affine atlas of the glued scheme indexed by finitely many tuples when the
ambient variable set is finite. In particular the parameter scheme is
quasi-compact; this does not assert that it is affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
set_option backward.isDefEq.respectTransparency false

universe u
variable (R I : Type u) [CommRing R] (d : ℕ)
variable (S : Type u) [CommRing S] [Algebra R S]
variable (f : Spec (.of S) ⟶ polynomialHilbertScheme R I d)
  (hf : f ≫ polynomialHilbertStructure R I d =
    Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- An arbitrary affine parameter factors through the bounded chart on its intrinsic locus. -/
theorem boundedPolynomialParameter_restrict (m : Fin d → BoundedHilbertMonomials I d) :
    let J := polynomialParameterIdeal R I d S f hf
    Scheme.Opens.ι (X := Spec (.of S))
      (polynomialBasisOpen R I d (fun i ↦ MvPolynomial.monomial (m i).val 1) S J) ≫ f =
      intrinsicChartMorphism R I d (fun i ↦ MvPolynomial.monomial (m i).val 1) S J ≫
        polynomialHilbertChartι R I d (fun i ↦ MvPolynomial.monomial (m i).val 1) := by
  dsimp only
  conv_lhs => rhs; rw [← polynomialParameterClassifyingMorphism_eq R I d S f hf]
  exact polynomialFamilyMorphism_restrict R I d S _
    (polynomialParameterIdeal_residueRank R I d S f hf) (fun i ↦ (m i).val)

include hf in
/-- Every point in every affine parameter image belongs to a bounded monomial chart. -/
theorem exists_boundedPolynomialChart_of_affine_parameter (x : Spec (.of S)) :
    ∃ m : Fin d → BoundedHilbertMonomials I d,
      f x ∈ Set.range
        (polynomialHilbertChartι R I d (fun i ↦ MvPolynomial.monomial (m i).val 1)) := by
  let J := polynomialParameterIdeal R I d S f hf
  obtain ⟨m, hm⟩ := exists_boundedMonomial_basisOpen R I S J x d
    (polynomialParameterIdeal_residueRank R I d S f hf x)
  let y : polynomialBasisScheme R I d
      (fun i ↦ MvPolynomial.monomial (m i).val 1) S J := ⟨x, hm⟩
  refine ⟨m, intrinsicChartMorphism R I d
    (fun i ↦ MvPolynomial.monomial (m i).val 1) S J y, ?_⟩
  exact (congrArg (fun g ↦ g y) (boundedPolynomialParameter_restrict R I d S f hf m)).symm

/-- Every point of the actual glued Hilbert scheme lies in a uniformly bounded chart. -/
theorem exists_boundedPolynomialHilbertChart (x : polynomialHilbertScheme R I d) :
    ∃ m : Fin d → BoundedHilbertMonomials I d,
      x ∈ Set.range
        (polynomialHilbertChartι R I d (fun i ↦ MvPolynomial.monomial (m i).val 1)) := by
  obtain ⟨w, y, hy⟩ := (polynomialHilbertSchemeCover R I d).exists_eq x
  change polynomialHilbertChartι R I d w y = x at hy
  rw [← hy]
  exact exists_boundedPolynomialChart_of_affine_parameter R I d (ChartRing R I d w)
    (polynomialHilbertChartι R I d w) (polynomialHilbertChartι_over R I d w) y

/-- The original affine chart spectra for bounded monomial tuples already cover the scheme. -/
def boundedPolynomialHilbertCover : (polynomialHilbertScheme R I d).OpenCover where
  I₀ := Fin d → BoundedHilbertMonomials I d
  X m := Spec (.of (ChartRing R I d (fun i ↦ MvPolynomial.monomial (m i).val 1)))
  f m := polynomialHilbertChartι R I d (fun i ↦ MvPolynomial.monomial (m i).val 1)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨exists_boundedPolynomialHilbertChart R I d, fun _ ↦ inferInstance⟩

instance [Finite I] : Finite (boundedPolynomialHilbertCover R I d).I₀ :=
  inferInstanceAs (Finite (Fin d → BoundedHilbertMonomials I d))

instance (m : (boundedPolynomialHilbertCover R I d).I₀) :
    IsAffine ((boundedPolynomialHilbertCover R I d).X m) :=
  inferInstanceAs (IsAffine (Spec _))

/-- A finite ambient variable set gives quasi-compactness of the actual Hilbert parameter scheme. -/
instance polynomialHilbertScheme_compactSpace [Finite I] :
    CompactSpace (polynomialHilbertScheme R I d) :=
  (boundedPolynomialHilbertCover R I d).compactSpace

end FLT.Mazur.HilbertChart
