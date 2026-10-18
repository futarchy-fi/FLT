/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeBadAffineCoverDenominators
public import FLT.Mazur.OriginalPrimeIntegralFiber

/-!
# Local integrality on the constructed bad atlas

Only the finitely many affine bad-chart scalar maps are localized. Empty
original fibers then give exact kernel scalars, whose product cuts out a
usable principal neighborhood in the unchanged, possibly nonaffine scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeBadAffineCover
open SchemeScalarPrincipalNeighborhood OriginalPrimeIntegralFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X : Scheme.{0}} [NoetherianSpace X]
  (s : R →+* Γ(X, ⊤)) (O : X.Opens) (P : PrimeSpectrum R)

/-- Local integral bad charts with empty original fibers have exact kernel separators. -/
theorem exists_badChart_kernel_separators
    (hInt : ∀ i, (localizedMap (badChartScalar s O i) P.asIdeal).IsIntegral)
    (hP : ∀ x : X, scalarMorphism s x = P → x ∈ O) :
    ∃ a : (badCover O).I₀ → R,
      ∀ i, a i ∉ P.asIdeal ∧ badChartScalar s O i (a i) = 0 := by
  classical
  have hex (i : (badCover O).I₀) :
      ∃ a : R, a ∉ P.asIdeal ∧ badChartScalar s O i a = 0 := by
    apply exists_kernel_scalar _ P.asIdeal (hInt i)
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

/-- A product on the actual bad atlas constructs one original denominator. -/
theorem exists_scalar_of_badChart_local_integral
    (hInt : ∀ i, (localizedMap (badChartScalar s O i) P.asIdeal).IsIntegral)
    (hP : ∀ x : X, scalarMorphism s x = P → x ∈ O) :
    ∃ r : R, r ∉ P.asIdeal ∧ X.basicOpen (s r) ≤ O := by
  obtain ⟨a, ha⟩ := exists_badChart_kernel_separators s O P hInt hP
  exact ⟨∏ i, a i, badChart_kernel_product s O P a ha⟩

/-- Locally integral bad charts make the exact original fiber test sufficient and necessary. -/
theorem mem_scalarNeighborhoodLocus_iff_badChart_local_integral
    (hInt : ∀ i, (localizedMap (badChartScalar s O i) P.asIdeal).IsIntegral) :
    P ∈ scalarNeighborhoodLocus s O ↔
      ∀ x : X, scalarMorphism s x = P → x ∈ O := by
  constructor
  · intro h x hx
    by_contra hn
    exact h (subset_closure ⟨x, hn, hx⟩)
  · intro h
    exact (mem_scalarNeighborhoodLocus_iff s O P).mpr
      (exists_scalar_of_badChart_local_integral s O P hInt h)

end FLT.Mazur.SchemeBadAffineCover
