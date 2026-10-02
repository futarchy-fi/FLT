/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.InertiaDescentField
public import FLT.AbsoluteGaloisGroup.LocalCyclotomicCharacter
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# Uniformizers in the unramified inertia descent ring

Ramification index one prevents a base uniformizer from lying in the square
of the extended maximal ideal. In particular the original rational prime
remains a uniformizer in the finite ring constructed by inertia descent.
-/

@[expose] public noncomputable section

open IsLocalRing IsDiscreteValuationRing

namespace IsDiscreteValuationRing

/-- An unramified local extension of Dedekind domains preserves uniformizers. -/
theorem irreducible_map_of_ramificationIdx_eq_one
    {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDedekindDomain S] [IsLocalRing S] [Algebra R S]
    [Module.IsTorsionFree R S] [(maximalIdeal S).LiesOver (maximalIdeal R)]
    {π : R} (hπ : Irreducible π) (he : (maximalIdeal S).ramificationIdx R = 1) :
    Irreducible (algebraMap R S π) := by
  have hle : (maximalIdeal R).map (algebraMap R S) ≤ maximalIdeal S :=
    Ideal.map_le_iff_le_comap.mpr (Ideal.over_def _ _).le
  have he' : (maximalIdeal R).ramificationIdx' (maximalIdeal S) = 1 :=
    (Ideal.ramificationIdx'_eq_ramificationIdx _ _ (not_a_field R)).trans he
  have hn : ¬ (maximalIdeal R).map (algebraMap R S) ≤ maximalIdeal S ^ 2 := by
    rw [← Ideal.ramificationIdx'_ne_one_iff hle, he']
    exact not_not.mpr rfl
  refine ⟨hle (Ideal.mem_map_of_mem _ hπ.not_isUnit), ?_⟩
  intro a b hab
  by_contra! h
  apply hn
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.span_le]
  rintro x (rfl : x = algebraMap R S π)
  rw [hab, pow_two]
  exact Ideal.mul_mem_mul h.1 h.2

end IsDiscreteValuationRing

open NumberField

variable {F X : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) [AddCommGroup X]
    [DistribMulAction (AlgebraicClosure (v.adicCompletion F) ≃ₐ[v.adicCompletion F]
      AlgebraicClosure (v.adicCompletion F)) X]
    [Finite X] [ContinuousSMulDiscrete (AlgebraicClosure (v.adicCompletion F) ≃ₐ[v.adicCompletion F]
      AlgebraicClosure (v.adicCompletion F)) X]

local notation "R" => v.adicCompletionIntegers F
local notation "S" => IntegralClosure R (InertiaDescent.field (X := X) (localInertiaGroup v))

/-- The actual inertia descent extension preserves every original uniformizer. -/
theorem inertiaDescentIntegers_irreducible {π : R} (hπ : Irreducible π) :
    Irreducible (algebraMap R S π) := by
  apply irreducible_map_of_ramificationIdx_eq_one hπ
  exact inertiaDescentField_ramificationIdx_eq_one v

/-- The finite integral closure used for descent is a DVR, not a field. -/
instance inertiaDescentIntegers_dvr : IsDiscreteValuationRing S where
  not_a_field' := by
    obtain ⟨π, hπ⟩ := exists_irreducible R
    intro h
    have hm : algebraMap R S π ∈ maximalIdeal S :=
      (inertiaDescentIntegers_irreducible v hπ).not_isUnit
    rw [h, Ideal.mem_bot] at hm
    exact (inertiaDescentIntegers_irreducible v hπ).ne_zero hm

set_option backward.isDefEq.respectTransparency.types false in
/-- At the rational p-adic place, p itself remains irreducible after descent. -/
theorem inertiaDescentIntegers_prime_irreducible (p : ℕ) [Fact p.Prime]
    {Y : Type} [AddCommGroup Y]
    [DistribMulAction (AlgebraicClosure ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)
      ≃ₐ[(LocalCyclotomic.rationalPlace p).adicCompletion ℚ]
      AlgebraicClosure ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)) Y]
    [Finite Y] [ContinuousSMulDiscrete
      (AlgebraicClosure ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)
      ≃ₐ[(LocalCyclotomic.rationalPlace p).adicCompletion ℚ]
      AlgebraicClosure ((LocalCyclotomic.rationalPlace p).adicCompletion ℚ)) Y] :
    Irreducible (p : IntegralClosure ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
      (InertiaDescent.field (X := Y) (localInertiaGroup (LocalCyclotomic.rationalPlace p)))) := by
  let e : ℤ_[p] ≃+* (LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ :=
    (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) ⟨p, Fact.out⟩).toAlgEquiv.toRingEquiv
  have hp : Irreducible (p : (LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ) := by
    simpa only [map_natCast] using ((MulEquiv.irreducible_iff (f := e)).mpr PadicInt.irreducible_p)
  simpa only [map_natCast] using inertiaDescentIntegers_irreducible (X := Y) _ hp
