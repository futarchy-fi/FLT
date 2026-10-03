/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.AdicLocalizationEmbedding
public import FLT.PadicHodgeTheory.ComplexThetaQuotientTopology

/-! # Hausdorff coefficient topologies on the p-inverted integral theta quotients -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Invert p in the actual n-th integral theta quotient. -/
abbrev ComplexThetaQuotientInvertP (n : ℕ) :=
  Localization.Away (p : ComplexIntegralThetaQuotient p n)

/-- No information is lost on passing from the integral quotient to its p-inversion. -/
theorem complexThetaQuotientInvertP_injective (n : ℕ) :
    Function.Injective (algebraMap (ComplexIntegralThetaQuotient p n)
      (ComplexThetaQuotientInvertP p n)) := by
  apply IsLocalization.injective (M := Submonoid.powers (p : ComplexIntegralThetaQuotient p n))
  rintro x ⟨k, rfl⟩
  apply Submonoid.pow_mem
  exact mem_nonZeroDivisors_iff_left.mpr (complexIntegralThetaQuotient_prime_mul_eq_zero p n)

/-- Neighborhoods are images of integral p-power ideals, not ideals of the localization. -/
scoped instance complexThetaQuotientInvertPTopology (n : ℕ) :
    TopologicalSpace (ComplexThetaQuotientInvertP p n) :=
  adicLocalizationTopology (p : ComplexIntegralThetaQuotient p n)
    (ComplexThetaQuotientInvertP p n)

/-- Multiplication is continuous by the proved denominator-clearing basis argument. -/
scoped instance complexThetaQuotientInvertP_isTopologicalRing (n : ℕ) :
    IsTopologicalRing (ComplexThetaQuotientInvertP p n) :=
  adicLocalization_isTopologicalRing _ _

/-- The p-inverted coefficient topology is Hausdorff. -/
scoped instance complexThetaQuotientInvertP_t2Space (n : ℕ) :
    T2Space (ComplexThetaQuotientInvertP p n) :=
  adicLocalization_t2Space _ _ (complexThetaQuotientInvertP_injective p n)

/-- The actual integral inclusion is continuous. -/
theorem complexThetaQuotientInvertP_continuous (n : ℕ) :
    Continuous (algebraMap (ComplexIntegralThetaQuotient p n)
      (ComplexThetaQuotientInvertP p n)) :=
  adicLocalization_algebraMap_continuous _ _ rfl

/-- The localized topology restricts to exactly the integral quotient topology. -/
theorem complexThetaQuotientInvertP_isOpenEmbedding (n : ℕ) :
    Topology.IsOpenEmbedding (algebraMap (ComplexIntegralThetaQuotient p n)
      (ComplexThetaQuotientInvertP p n)) :=
  adicLocalization_isOpenEmbedding _ _ rfl (complexThetaQuotientInvertP_injective p n)

/-- The canonical transition after inverting p. -/
def complexThetaQuotientInvertPTransition {m n : ℕ} (h : n ≤ m) :
    ComplexThetaQuotientInvertP p m →+* ComplexThetaQuotientInvertP p n := by
  let f := Ideal.Quotient.factorPow (RingHom.ker (complexTheta p)) h
  let : IsLocalization.Away (f p) (ComplexThetaQuotientInvertP p n) := by
    simpa only [map_natCast] using
      (inferInstance : IsLocalization.Away (p : ComplexIntegralThetaQuotient p n)
        (ComplexThetaQuotientInvertP p n))
  exact IsLocalization.Away.map _ _ f (p : ComplexIntegralThetaQuotient p m)

/-- The localized transition agrees with the actual integral quotient transition. -/
@[simp] theorem complexThetaQuotientInvertPTransition_algebraMap {m n : ℕ} (h : n ≤ m)
    (a : ComplexIntegralThetaQuotient p m) :
    complexThetaQuotientInvertPTransition p h (algebraMap _ _ a) =
      algebraMap _ _ (Ideal.Quotient.factorPow (RingHom.ker (complexTheta p)) h a) :=
  by
  simp only [complexThetaQuotientInvertPTransition, IsLocalization.Away.map, IsLocalization.map_eq]

/-- All localized transitions are continuous in the coefficient topologies. -/
theorem complexThetaQuotientInvertPTransition_continuous {m n : ℕ} (h : n ≤ m) :
    Continuous (complexThetaQuotientInvertPTransition p h) := by
  apply adicLocalization_continuous_of_lattice (p : ComplexIntegralThetaQuotient p m)
    (ComplexThetaQuotientInvertP p m) (p : ComplexIntegralThetaQuotient p n)
  intro k x hx
  obtain ⟨a, rfl⟩ := (mem_adicLocalizationLattice _ _ k x).mp hx
  rw [complexThetaQuotientInvertPTransition_algebraMap]
  apply (mem_adicLocalizationLattice _ _ k _).mpr
  refine ⟨Ideal.Quotient.factorPow (RingHom.ker (complexTheta p)) h a, ?_⟩
  simp only [map_mul, map_pow, map_natCast]

/-- Powers of p tend to zero even after p is inverted. -/
theorem complexThetaQuotientInvertP_prime_pow_tendsto (n : ℕ) :
    Filter.Tendsto (fun k : ℕ ↦ (p : ComplexThetaQuotientInvertP p n) ^ k)
      Filter.atTop (nhds 0) := by
  have h := (complexThetaQuotientInvertP_continuous p n).continuousAt.tendsto.comp
    (complexIntegralThetaQuotient_prime_pow_tendsto p n)
  simpa only [Function.comp_def, map_pow, map_natCast, map_zero] using h

end PadicHodgeTheory
