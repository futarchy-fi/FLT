/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertUniversalComplementMatrix
public import FLT.Mazur.HilbertBoundedPolynomialAtlas

/-!
# Repeated monomial tuples give empty Hilbert charts

At every actual chart point the coefficient ring is nontrivial, so the
prescribed quotient basis forces the monomial tuple to be injective.
Consequently the existing bounded atlas is covered by its injective tuples.
-/

@[expose] public noncomputable section
open AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
set_option backward.isDefEq.respectTransparency false
universe u
variable (R I : Type u) [CommRing R] (d : ℕ)
  (m : Fin d → BoundedHilbertMonomials I d)
local notation "w" => (fun a ↦ MvPolynomial.monomial (Subtype.val (m a)) (1 : R))
local notation "C" => ChartRing R I d w

/-- Cache the original coefficient ring. -/
local instance repeatedMonomialCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache the original chart ring. -/
local instance repeatedMonomialChartRing : CommRing C := inferInstance

/-- A prescribed monomial basis over a nonzero original chart ring has no repeated columns. -/
theorem monomialTuple_injective_of_chartNontrivial [Nontrivial C] : Function.Injective m := by
  intro i j hij
  apply (chartIdentityBasis R I d w).injective
  rw [← chartIdentityBasis_monomial R I d m i, ← chartIdentityBasis_monomial R I d m j, hij]

/-- Any actual chart point forces injectivity of the selected original monomial tuple. -/
theorem monomialTuple_injective_of_chartPoint (p : Spec (.of C)) : Function.Injective m := by
  let _ := PrimeSpectrum.nontrivial p
  exact monomialTuple_injective_of_chartNontrivial R I d m

/-- A repeated monomial tuple has an empty actual chart spectrum. -/
theorem monomialChart_isEmpty_of_not_injective (hm : ¬ Function.Injective m) :
    IsEmpty (Spec (.of C)) :=
  ⟨fun p ↦ hm (monomialTuple_injective_of_chartPoint R I d m p)⟩

/-- Every original Hilbert point lies in a chart with an injective bounded monomial tuple. -/
theorem exists_injectiveBoundedPolynomialHilbertChart (x : polynomialHilbertScheme R I d) :
    ∃ (n : Fin d → BoundedHilbertMonomials I d), Function.Injective n ∧
      x ∈ Set.range
        (polynomialHilbertChartι R I d (fun i ↦ MvPolynomial.monomial (n i).val 1)) := by
  obtain ⟨n, p, hp⟩ := exists_boundedPolynomialHilbertChart R I d x
  exact ⟨n, monomialTuple_injective_of_chartPoint R I d n p, p, hp⟩

end FLT.Mazur.HilbertChart
