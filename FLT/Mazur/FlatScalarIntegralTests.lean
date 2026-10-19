/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarTestIntegralFibers
public import FLT.Mazur.FlatScalarTestDenominators

/-!
# Constructing full scalar equations from integral flat branch test charts

Exact original fiber tests ascend to every scalar extension. Local integrality
of the full branch principal charts then constructs actual branch equations;
flatness descends them to original equations, before any reduction.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ScalarTestLocalization
open OriginalPrimeIntegralFiber
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
  (S : Type*) [CommRing S] [Algebra R S]
local notation "B'" => S ⊗[R] B
local notation "j" => Algebra.TensorProduct.includeRight (R := R) (A := S) (B := B)

/-- The full branch test-chart scalar map, retaining the original coefficient tensor algebra. -/
def flatTestScalar (b : B) : S →+* Localization.Away (j b) :=
  (algebraMap B' (Localization.Away (j b))).comp (algebraMap S B')

/-- Exact original fiber tests ascend without flatness or a finite presentation hypothesis. -/
theorem flatTensor_fiber_test (Q : PrimeSpectrum S) (b : B)
    (hf : ∀ q : PrimeSpectrum B, PrimeSpectrum.comap (algebraMap R B) q =
      PrimeSpectrum.comap (algebraMap R S) Q → b ∈ q.asIdeal)
    (q : PrimeSpectrum B') (hq : PrimeSpectrum.comap (algebraMap S B') q = Q) :
    j b ∈ q.asIdeal := by
  apply hf (PrimeSpectrum.comap (j).toRingHom q)
  have hc : (j).toRingHom.comp (algebraMap R B) =
      (algebraMap S B').comp (algebraMap R S) := by
    ext r
    exact ((j).commutes r).trans (IsScalarTower.algebraMap_apply R S B' r)
  apply PrimeSpectrum.ext
  change q.asIdeal.comap ((j).toRingHom.comp (algebraMap R B)) = _
  rw [hc, ← Ideal.comap_comap]
  exact congrArg (fun p : PrimeSpectrum S ↦ p.asIdeal.comap (algebraMap R S)) hq

/-- Integral branch test charts and exact original fibers construct full branch power equations. -/
theorem tensor_equation_of_integral_test (Q : PrimeSpectrum S) (b : B)
    (hi : (localizedMap (flatTestScalar (R := R) S b) Q.asIdeal).IsIntegral)
    (hf : ∀ q : PrimeSpectrum B, PrimeSpectrum.comap (algebraMap R B) q =
      PrimeSpectrum.comap (algebraMap R S) Q → b ∈ q.asIdeal) :
    ∃ (x : S) (k : ℕ), x ∉ Q.asIdeal ∧ (j b) ^ k * algebraMap S B' x = 0 :=
  equation_of_integral_testChart (algebraMap S B') Q (j b) hi
    (flatTensor_fiber_test S Q b hf)

/-- Original branch generator polynomials construct power equations on the full tensor algebra. -/
theorem tensor_equation_of_generator_polynomials (Q : PrimeSpectrum S) (b : B)
    (G : Set (Localization.Away (j b)))
    (hG : Subring.closure (Set.range (flatTestScalar (R := R) S b) ∪ G) = ⊤)
    (hg : ∀ x ∈ G, ∃ p : Polynomial S,
      p.eval₂ (flatTestScalar (R := R) S b) x = 0 ∧ p.leadingCoeff ∉ Q.asIdeal)
    (hf : ∀ q : PrimeSpectrum B, PrimeSpectrum.comap (algebraMap R B) q =
      PrimeSpectrum.comap (algebraMap R S) Q → b ∈ q.asIdeal) :
    ∃ (x : S) (k : ℕ), x ∉ Q.asIdeal ∧ (j b) ^ k * algebraMap S B' x = 0 :=
  equation_of_testChart_generators (algebraMap S B') Q (j b) G hG hg
    (flatTensor_fiber_test S Q b hf)

variable [Module.Flat R S]

/-- The constructed branch equation yields an equation in the unchanged original algebra. -/
theorem original_equation_of_integral_flat_test (Q : PrimeSpectrum S) (b : B)
    (hi : (localizedMap (flatTestScalar (R := R) S b) Q.asIdeal).IsIntegral)
    (hf : ∀ q : PrimeSpectrum B, PrimeSpectrum.comap (algebraMap R B) q =
      PrimeSpectrum.comap (algebraMap R S) Q → b ∈ q.asIdeal) :
    ∃ (r : R) (k : ℕ), r ∉ Q.asIdeal.comap (algebraMap R S) ∧
      b ^ k * algebraMap R B r = 0 := by
  obtain ⟨x, k, hx, he⟩ := tensor_equation_of_integral_test S Q b hi hf
  obtain ⟨r, hr, hm⟩ := FlatScalarPowerKernel.original_equation_same_power S Q b k x hx he
  exact ⟨r, k, hr, hm⟩

/-- Independent integral principal tests construct one original whole-ideal power denominator. -/
theorem original_denominator_of_integral_flat_tests (Q : PrimeSpectrum S) (a : Finset B)
    (hi : ∀ b ∈ a, (localizedMap (flatTestScalar (R := R) S b) Q.asIdeal).IsIntegral)
    (hf : ∀ q : PrimeSpectrum B, PrimeSpectrum.comap (algebraMap R B) q =
      PrimeSpectrum.comap (algebraMap R S) Q → ∀ b ∈ a, b ∈ q.asIdeal) :
    ∃ (k : ℕ) (r : R), r ∉ Q.asIdeal.comap (algebraMap R S) ∧
      algebraMap R B r ∈ ((Ideal.span (a : Set B)) ^ k).annihilator := by
  apply original_power_denominator_of_flat S a Q
  intro b hb
  exact tensor_equation_of_integral_test S Q b (hi b hb) (fun q hq ↦ hf q hq b hb)

end FLT.Mazur.ScalarTestLocalization
