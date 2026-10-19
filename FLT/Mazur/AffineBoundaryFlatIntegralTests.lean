/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBoundaryFlatTensorEquations
public import FLT.Mazur.FlatScalarIntegralTests

/-!
# Constructing boundary tensor equations from integral branch test charts

Matching exact original fibers and local integrality of full flat branch
principal charts construct the power equations used by scalar descent.
Neither an equation after reduction nor integrality of just the full
boundary algebra is substituted for these principal-chart obligations.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
open ScalarTestLocalization OriginalPrimeIntegralFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryProduct boundaryCoordinate
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T)
set_option quotPrecheck false
local notation "C" => Γ(boundaryProduct s κ, ⊤)
local notation "σ" => boundaryScalarHom s κ
/-- The full boundary coordinates carry the unchanged original scalar action. -/
local instance boundaryIntegralTensorAlgebra : Algebra T C := (σ).toAlgebra
variable (S : Type) [CommRing S] [Algebra T S]

/-- The full branch principal chart, with scalars from the chosen extension. -/
def boundaryFlatTestScalar (t : B) : S →+*
    Localization.Away (Algebra.TensorProduct.includeRight
      (R := T) (A := S) (B := C) (boundaryCoordinate s κ t)) :=
  flatTestScalar (R := T) S (boundaryCoordinate s κ t)

omit S [CommRing S] [Algebra T S] in
/-- Exact geometric tests give exact coordinate-prime tests on the original full product. -/
theorem boundary_coordinate_fiber_tests (a : Finset B) (P : PrimeSpectrum T)
    (hf : ∀ z : boundaryProduct s κ, boundaryScalarProjection s κ z = P →
      ∀ t ∈ a, t ∈ (boundaryProjection s κ z).asIdeal)
    (q : PrimeSpectrum C) (hq : PrimeSpectrum.comap σ q = P) :
    ∀ t ∈ a, boundaryCoordinate s κ t ∈ q.asIdeal := by
  let z := (boundaryProduct s κ).isoSpec.inv q
  have hz : (boundaryProduct s κ).isoSpec.hom z = q :=
    congrArg (fun f ↦ f q) (boundaryProduct s κ).isoSpec.inv_hom_id
  have hp : boundaryScalarProjection s κ z = P := by
    apply PrimeSpectrum.ext
    rw [← boundaryScalarHom_comap_point, hz]
    exact congrArg PrimeSpectrum.asIdeal hq
  have ht := (boundaryTestIdeal_le_point_iff s κ a z).mpr (hf z hp)
  rw [hz] at ht
  exact fun t ht' ↦ ht (boundaryCoordinate_mem_testIdeal s κ a ht')

/-- Full branch equations are constructed from integrality and exact original fiber geometry. -/
theorem boundary_tensor_equations_of_integral_tests (a : Finset B) (Q : PrimeSpectrum S)
    (hi : ∀ t ∈ a, (localizedMap (boundaryFlatTestScalar s κ S t) Q.asIdeal).IsIntegral)
    (hf : ∀ z : boundaryProduct s κ, boundaryScalarProjection s κ z =
      PrimeSpectrum.comap (algebraMap T S) Q →
      ∀ t ∈ a, t ∈ (boundaryProjection s κ z).asIdeal) :
    ∀ t ∈ a, ∃ (x : S) (k : ℕ), x ∉ Q.asIdeal ∧
      boundaryTensorPowerEquation s κ S t x k := by
  intro t ht
  exact tensor_equation_of_integral_test S Q (boundaryCoordinate s κ t) (hi t ht)
    (fun q hq ↦ boundary_coordinate_fiber_tests s κ a _ hf q hq t ht)

variable [Module.Flat T S]

/-- Constructed equations exclude all original generizing obstructions at the contracted prime. -/
theorem boundaryScalar_mem_of_integral_flat_tests (a : Finset B) (Q : PrimeSpectrum S)
    (hi : ∀ t ∈ a, (localizedMap (boundaryFlatTestScalar s κ S t) Q.asIdeal).IsIntegral)
    (hf : ∀ z : boundaryProduct s κ, boundaryScalarProjection s κ z =
      PrimeSpectrum.comap (algebraMap T S) Q →
      ∀ t ∈ a, t ∈ (boundaryProjection s κ z).asIdeal) :
    PrimeSpectrum.comap (algebraMap T S) Q ∈ boundaryScalarNilpotenceOpen s κ a :=
  boundaryScalar_mem_of_flat_tensor_equations s κ S a Q
    (boundary_tensor_equations_of_integral_tests s κ S a Q hi hf)

/-- The construction gives a scalar annihilating a whole original test-ideal power. -/
theorem boundary_denominator_of_integral_flat_tests (a : Finset B) (Q : PrimeSpectrum S)
    (hi : ∀ t ∈ a, (localizedMap (boundaryFlatTestScalar s κ S t) Q.asIdeal).IsIntegral)
    (hf : ∀ z : boundaryProduct s κ, boundaryScalarProjection s κ z =
      PrimeSpectrum.comap (algebraMap T S) Q →
      ∀ t ∈ a, t ∈ (boundaryProjection s κ z).asIdeal) :
    ∃ (k : ℕ) (r : T), r ∉ Q.asIdeal.comap (algebraMap T S) ∧
      σ r ∈ ((boundaryTestIdeal s κ a) ^ k).annihilator :=
  boundary_denominator_of_flat_tensor_equations s κ S a Q
    (boundary_tensor_equations_of_integral_tests s κ S a Q hi hf)

omit [Module.Flat T S] in
/-- Faithful flatness constructs the branch point needed by the integral-test argument. -/
theorem boundaryScalar_mem_of_faithfully_flat_integral_tests
    [Module.FaithfullyFlat T S] (a : Finset B) (P : PrimeSpectrum T)
    (hi : ∀ Q : PrimeSpectrum S, PrimeSpectrum.comap (algebraMap T S) Q = P →
      ∀ t ∈ a, (localizedMap (boundaryFlatTestScalar s κ S t) Q.asIdeal).IsIntegral)
    (hf : ∀ z : boundaryProduct s κ, boundaryScalarProjection s κ z = P →
      ∀ t ∈ a, t ∈ (boundaryProjection s κ z).asIdeal) :
    P ∈ boundaryScalarNilpotenceOpen s κ a := by
  apply boundaryScalar_mem_of_faithfully_flat_tensor s κ S a P
  intro Q hQ
  apply boundary_tensor_equations_of_integral_tests s κ S a Q (hi Q hQ)
  simpa only [hQ] using hf

end FLT.Mazur.AffineScalarBoundaryNilpotence
