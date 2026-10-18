/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeBadAffineCoverFiniteType
public import FLT.Mazur.SchemeBadAffineCoverLocalIntegral
public import FLT.Mazur.OriginalPrimeIntegralGenerators

/-!
# Finite equations on the constructed affine bad atlas

The charts and their algebra generators are already constructed. Polynomial
equations for these generators give one product of leading coefficients.
On its original principal locus, whole-fiber containment constructs a safe
original denominator without any affine ambient relation hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeBadAffineCover
open SchemeScalarPrincipalNeighborhood OriginalPrimeIntegralFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X : Scheme.{0}} [NoetherianSpace X]
  (s : R →+* Γ(X, ⊤)) (O : X.Opens)
  (g : X ⟶ Spec (.of ℤ)) [LocallyOfFiniteType g]
attribute [local irreducible] badChartGenerators
local notation "G" => badChartGenerators s O g

/-- A single original scalar controls all equations on all constructed bad charts. -/
def badChartLeadingProduct (p : ∀ i : (badCover O).I₀, G i → Polynomial R) : R := by
  classical
  exact ∏ i : (badCover O).I₀, ∏ b : G i, (p i b).leadingCoeff

variable (p : ∀ i : (badCover O).I₀, badChartGenerators s O g i → Polynomial R)

/-- Every chosen generator has an equation with leading coefficient outside the original prime. -/
theorem badChart_generator_equations (P : PrimeSpectrum R)
    (heq : ∀ (i : (badCover O).I₀) (b : G i), (p i b).eval₂ (badChartScalar s O i) b.val = 0)
    (hlead : badChartLeadingProduct s O g p ∉ P.asIdeal) (i : (badCover O).I₀) :
    ∀ b ∈ (G i : Set Γ((badCover O).X i, ⊤)), ∃ q : Polynomial R,
      q.eval₂ (badChartScalar s O i) b = 0 ∧ q.leadingCoeff ∉ P.asIdeal := by
  classical
  intro b hb
  refine ⟨p i ⟨b, hb⟩, heq i ⟨b, hb⟩, ?_⟩
  intro h
  apply hlead
  change (∏ j : (badCover O).I₀, ∏ a : G j, (p j a).leadingCoeff) ∈ P.asIdeal
  exact Ideal.IsPrime.prod_mem_iff.mpr ⟨i, Finset.mem_univ i,
    Ideal.IsPrime.prod_mem_iff.mpr ⟨⟨b, hb⟩, Finset.mem_univ _, h⟩⟩

/-- Actual generator equations yield one exact kernel separator per bad chart. -/
theorem exists_badChart_kernel_separators_of_equations (P : PrimeSpectrum R)
    (heq : ∀ (i : (badCover O).I₀) (b : G i), (p i b).eval₂ (badChartScalar s O i) b.val = 0)
    (hlead : badChartLeadingProduct s O g p ∉ P.asIdeal)
    (hP : ∀ x : X, scalarMorphism s x = P → x ∈ O) :
    ∃ a : (badCover O).I₀ → R,
      ∀ i, a i ∉ P.asIdeal ∧ badChartScalar s O i (a i) = 0 := by
  classical
  have hex (i : (badCover O).I₀) :
      ∃ a : R, a ∉ P.asIdeal ∧ badChartScalar s O i a = 0 := by
    apply exists_kernel_scalar_of_generator_equations (badChartScalar s O i) P.asIdeal
      (G i : Set Γ((badCover O).X i, ⊤)) (badChartGenerators_generate s O g i)
      (badChart_generator_equations s O g p P heq hlead i)
    intro Q hQ
    obtain ⟨y, hy⟩ := ((badCover O).X i).toSpecΓ.homeomorph.surjective Q
    change ((badCover O).X i).toSpecΓ y = Q at hy
    have he : scalarMorphism (badChartScalar s O i) y = P := by
      change PrimeSpectrum.comap (badChartScalar s O i) (((badCover O).X i).toSpecΓ y) = P
      rw [hy]
      exact PrimeSpectrum.ext hQ
    rw [badChartScalar, scalarMorphism_comp] at he
    exact badChartMap_not_mem O i y (hP _ he)
  choose a ha using hex
  exact ⟨a, ha⟩

/-- Actual bad-chart equations and a complete original fiber construct a denominator. -/
theorem exists_scalar_of_badChart_equations (P : PrimeSpectrum R)
    (heq : ∀ (i : (badCover O).I₀) (b : G i), (p i b).eval₂ (badChartScalar s O i) b.val = 0)
    (hlead : badChartLeadingProduct s O g p ∉ P.asIdeal)
    (hP : ∀ x : X, scalarMorphism s x = P → x ∈ O) :
    ∃ r : R, r ∉ P.asIdeal ∧ X.basicOpen (s r) ≤ O := by
  obtain ⟨a, ha⟩ := exists_badChart_kernel_separators_of_equations s O g p P heq hlead hP
  exact ⟨∏ i, a i, badChart_kernel_product s O P a ha⟩

/-- The constructed leading-coefficient open turns the exact fiber test into full safety. -/
theorem mem_scalarNeighborhoodLocus_iff_badChart_equations (P : PrimeSpectrum R)
    (heq : ∀ (i : (badCover O).I₀) (b : G i), (p i b).eval₂ (badChartScalar s O i) b.val = 0)
    (hlead : badChartLeadingProduct s O g p ∉ P.asIdeal) :
    P ∈ scalarNeighborhoodLocus s O ↔
      ∀ x : X, scalarMorphism s x = P → x ∈ O := by
  constructor
  · intro h x hx
    by_contra hn
    exact h (subset_closure ⟨x, hn, hx⟩)
  · intro h
    exact (mem_scalarNeighborhoodLocus_iff s O P).mpr
      (exists_scalar_of_badChart_equations s O g p P heq hlead h)

end FLT.Mazur.SchemeBadAffineCover
