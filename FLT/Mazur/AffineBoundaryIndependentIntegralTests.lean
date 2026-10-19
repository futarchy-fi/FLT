/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBoundaryFlatIntegralTests
public import FLT.Mazur.AffineBoundaryTestKernelDescent

/-!
# Independent integral test branches and a uniform residual scalar

Different tests can use different flat scalar algebras. The same original
exact fiber controls all of them. On a residual closed locus the constructed
coverage gives one scalar congruent to one modulo its defining ideal.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
open ScalarTestLocalization OriginalPrimeIntegralFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryProduct boundaryCoordinate
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T) (a : Finset B)
set_option quotPrecheck false
local notation "C" => Γ(boundaryProduct s κ, ⊤)
/-- The full boundary coordinates carry the unchanged original scalar action. -/
local instance boundaryIndependentIntegralAlgebra : Algebra T C :=
  (boundaryScalarHom s κ).toAlgebra

/-- Each test can use its own integral flat branch without changing the original scalar prime. -/
theorem boundaryScalar_mem_of_independent_integral_tests
    (Ss : a → Type) [∀ t, CommRing (Ss t)] [∀ t, Algebra T (Ss t)]
    [∀ t, Module.Flat T (Ss t)] (P : PrimeSpectrum T) (Qs : ∀ t, PrimeSpectrum (Ss t))
    (hQ : ∀ t, PrimeSpectrum.comap (algebraMap T (Ss t)) (Qs t) = P)
    (hi : ∀ t, (localizedMap (boundaryFlatTestScalar s κ (Ss t) t.val)
      (Qs t).asIdeal).IsIntegral)
    (hf : ∀ z : boundaryProduct s κ, boundaryScalarProjection s κ z = P →
      ∀ t ∈ a, t ∈ (boundaryProjection s κ z).asIdeal) :
    P ∈ boundaryScalarNilpotenceOpen s κ a := by
  apply boundaryScalar_mem_of_independent_flat_tensor s κ a Ss P Qs hQ
  intro t
  apply tensor_equation_of_integral_test (Ss t) (Qs t)
    (boundaryCoordinate s κ t.val) (hi t)
  intro q hq
  rw [hQ t] at hq
  exact boundary_coordinate_fiber_tests s κ a P hf q hq t.val t.property

/-- Independent integral branches produce one full original ideal-power denominator. -/
theorem boundary_denominator_of_independent_integral_tests
    (Ss : a → Type) [∀ t, CommRing (Ss t)] [∀ t, Algebra T (Ss t)]
    [∀ t, Module.Flat T (Ss t)] (P : PrimeSpectrum T) (Qs : ∀ t, PrimeSpectrum (Ss t))
    (hQ : ∀ t, PrimeSpectrum.comap (algebraMap T (Ss t)) (Qs t) = P)
    (hi : ∀ t, (localizedMap (boundaryFlatTestScalar s κ (Ss t) t.val)
      (Qs t).asIdeal).IsIntegral)
    (hf : ∀ z : boundaryProduct s κ, boundaryScalarProjection s κ z = P →
      ∀ t ∈ a, t ∈ (boundaryProjection s κ z).asIdeal) :
    ∃ (k : ℕ) (r : T), r ∉ P.asIdeal ∧
      boundaryScalarHom s κ r ∈ ((boundaryTestIdeal s κ a) ^ k).annihilator :=
  (mem_boundaryScalarNilpotenceOpen s κ a P).mp
    (boundaryScalar_mem_of_independent_integral_tests s κ a Ss P Qs hQ hi hf)

/-- Integral test branches over the full residual locus give a single normalized original scalar. -/
theorem boundary_residual_denominator_of_faithfully_flat_integral_tests
    (S : Type) [CommRing S] [Algebra T S] [Module.FaithfullyFlat T S] (J : Ideal T)
    (hi : ∀ Q : PrimeSpectrum S, J ≤ Q.asIdeal.comap (algebraMap T S) →
      ∀ t ∈ a, (localizedMap (boundaryFlatTestScalar s κ S t) Q.asIdeal).IsIntegral)
    (hf : ∀ (P : PrimeSpectrum T), J ≤ P.asIdeal →
      ∀ z : boundaryProduct s κ, boundaryScalarProjection s κ z = P →
      ∀ t ∈ a, t ∈ (boundaryProjection s κ z).asIdeal) :
    ∃ (r : T) (k : ℕ), 1 - r ∈ J ∧
      boundaryScalarHom s κ r ∈ ((boundaryTestIdeal s κ a) ^ k).annihilator ∧
      ∀ P : PrimeSpectrum T, J ≤ P.asIdeal → r ∉ P.asIdeal := by
  apply boundaryScalar_residual_uniform_denominator s κ a J
  intro P hP
  apply boundaryScalar_mem_of_faithfully_flat_integral_tests s κ S a P _ (hf P hP)
  intro Q hQ
  apply hi Q
  change J ≤ (PrimeSpectrum.comap (algebraMap T S) Q).asIdeal
  rwa [hQ]

end FLT.Mazur.AffineScalarBoundaryNilpotence
