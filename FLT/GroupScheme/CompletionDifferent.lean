/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalDifferentEquiv
public import FLT.NumberField.Completion.Different
public import FLT.NumberField.Completion.FieldEquiv

/-!
# The normalized different of a three-adic completion

Identify the completed integer ring with the integral closure of `ℤ_[3]`,
and compare the global and local normalizations of the different.
-/

@[expose] public noncomputable section

open NumberField IsDedekindDomain.HeightOneSpectrum UniqueFactorizationMonoid

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

namespace ThreeAdicPlan

/-- An isomorphism from a DVR to the three-adic integer ring preserves ideal order. -/
theorem threeAdicIdealOrder_map_ringEquiv
    {L R : Type*} [Field L] [Algebra ℚ_[3] L] [Algebra ℤ_[3] L]
    [IsScalarTower ℤ_[3] ℚ_[3] L] [FiniteDimensional ℚ_[3] L]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (e : R ≃+* ThreeAdicIntegers L) (I : Ideal R) :
    threeAdicIdealOrder L (I.map e.toRingHom) =
      (normalizedFactors I).count (IsLocalRing.maximalIdeal R) := by
  classical
  by_cases hI : I = ⊥
  · subst I
    rw [Ideal.map_bot]
    change (normalizedFactors (0 : Ideal (ThreeAdicIntegers L))).count _ =
      (normalizedFactors (0 : Ideal R)).count _
    simp only [normalizedFactors_zero, Multiset.count_zero]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, rfl⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hπ
  rw [← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq, Ideal.map_pow,
    IsLocalRing.map_maximalIdeal_of_surjective e.toRingHom e.surjective,
    threeAdicIdealOrder_pow, threeAdicIdealOrder_maximalIdeal, mul_one]
  have hp : Irreducible (IsLocalRing.maximalIdeal R) :=
    ((Ideal.prime_iff_isPrime (IsDiscreteValuationRing.not_a_field R)).mpr
      inferInstance).irreducible
  simp only [normalizedFactors_pow, Multiset.count_nsmul, normalizedFactors_irreducible hp,
    normalize_eq, Multiset.count_singleton_self, mul_one]

set_option backward.isDefEq.respectTransparency false in
/-- Global and completed different exponents agree, normalized by `v(3) = 1`,
for compatible presentations of the completed rational base and its integers. -/
theorem normalizedDifferentExponent_completion_eq
    {L : Type*} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (e : v.adicCompletion ℚ ≃ₐ[ℚ] ℚ_[3])
    (eO : v.adicCompletionIntegers ℚ ≃ₐ[ℤ] ℤ_[3])
    (heO : ∀ z : ℤ_[3], ((eO.symm z : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) =
      e.symm (z : ℚ_[3]))
    (w : v.Extension (𝓞 L)) (hw : (3 : 𝓞 L) ∈ w.1.asIdeal) :
    letI := completionAlgebraOfEquiv v e w
    letI : Algebra ℤ_[3] (w.1.adicCompletion L) := Algebra.compHom _ (algebraMap ℤ_[3] ℚ_[3])
    letI : IsScalarTower ℤ_[3] ℚ_[3] (w.1.adicCompletion L) := .of_algebraMap_eq' rfl
    letI := completion_finiteDimensional_of_equiv v e w
    normalizedDifferentExponent (w.1.adicCompletion L) =
      NumberField.normalizedDifferentExponentAt L w.1.asIdeal := by
  let := completionAlgebraOfEquiv v e w
  let : Algebra ℤ_[3] (w.1.adicCompletion L) :=
    Algebra.compHom _ (algebraMap ℤ_[3] ℚ_[3])
  let : IsScalarTower ℤ_[3] ℚ_[3] (w.1.adicCompletion L) := .of_algebraMap_eq' rfl
  let := completion_finiteDimensional_of_equiv v e w
  let : Algebra ℤ_[3] (v.adicCompletion ℚ) :=
    ((algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)).comp
      eO.symm.toRingHom).toAlgebra
  let : Algebra ℤ_[3] (w.1.adicCompletionIntegers L) :=
    ((algebraMap (v.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers L)).comp
      eO.symm.toRingHom).toAlgebra
  let : IsFractionRing ℤ_[3] (v.adicCompletion ℚ) :=
    IsFractionRing.of_ringEquiv_left eO.symm.toRingEquiv (fun _ ↦ rfl)
  let : IsScalarTower (v.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers L)
      (w.1.adicCompletion L) := .of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower ℤ_[3] (v.adicCompletion ℚ) (w.1.adicCompletion L) := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    change algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion L) (e.symm (z : ℚ_[3])) =
      algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion L) (eO.symm z)
    rw [heO]
  let : IsScalarTower ℤ_[3] (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    change algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion L) (e.symm (z : ℚ_[3])) =
      algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion L) (eO.symm z)
    rw [heO]
  let : Module.Finite ℤ_[3] (w.1.adicCompletionIntegers L) := by
    apply Module.Finite.of_equiv_equiv eO.toRingEquiv (RingEquiv.refl _)
    apply RingHom.ext
    intro z
    change algebraMap (v.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers L)
      (eO.symm (eO z)) = algebraMap (v.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers L) z
    rw [eO.symm_apply_apply]
  let : FaithfulSMul ℤ_[3] (w.1.adicCompletionIntegers L) :=
    FaithfulSMul.of_field_isFractionRing _ _ (v.adicCompletion ℚ) (w.1.adicCompletion L)
  let : Module.IsTorsionFree ℤ_[3] (w.1.adicCompletion L) :=
    .trans_faithfulSMul ℤ_[3] ℚ_[3] (w.1.adicCompletion L)
  let eI := IsIntegralClosure.equiv ℤ_[3] (w.1.adicCompletionIntegers L)
    (w.1.adicCompletion L) (ThreeAdicIntegers (w.1.adicCompletion L))
  have hd : differentIdeal (v.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers L) =
      differentIdeal ℤ_[3] (w.1.adicCompletionIntegers L) := by
    apply differentIdeal_eq_of_algebraMap_range_eq _ _ (v.adicCompletion ℚ)
      (w.1.adicCompletion L)
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨eO z, ?_⟩
      change (eO.symm (eO z) : v.adicCompletion ℚ) = _
      rw [eO.symm_apply_apply]
      rfl
    · rintro ⟨z, rfl⟩
      exact ⟨eO.symm z, rfl⟩
  have hm : (differentIdeal ℤ_[3] (w.1.adicCompletionIntegers L)).map eI.toRingHom =
      differentIdeal ℤ_[3] (ThreeAdicIntegers (w.1.adicCompletion L)) := by
    let pb := (threeAdicIntegersPowerBasis (w.1.adicCompletion L)).map eI.symm
    rw [pb.differentIdeal_eq_span_minpoly_derivative ℚ_[3] (w.1.adicCompletion L),
      (pb.map eI).differentIdeal_eq_span_minpoly_derivative ℚ_[3] (w.1.adicCompletion L),
      Ideal.map_span, Set.image_singleton]
    simp only [PowerBasis.map_gen, minpoly.algEquiv_eq]
    congr 2
    convert! (Polynomial.aeval_algHom_apply eI pb.gen
      (Polynomial.derivative (minpoly ℤ_[3] pb.gen))).symm using 1
  have hn := threeAdicIdealOrder_map_ringEquiv eI.toRingEquiv
    (differentIdeal ℤ_[3] (w.1.adicCompletionIntegers L))
  rw [hm, ← hd, NumberField.count_differentIdeal_completion L v w] at hn
  have h3 := threeAdicIdealOrder_map_ringEquiv eI.toRingEquiv
    (Ideal.span {(3 : w.1.adicCompletionIntegers L)})
  simp only [Ideal.map_span, Set.image_singleton, map_ofNat] at h3
  have hcount := w.1.count_normalizedFactors_map_completion L (Ideal.span {(3 : 𝓞 L)})
  simp only [Ideal.map_span, Set.image_singleton, map_ofNat] at hcount
  have : w.1.asIdeal.LiesOver (Ideal.span {(3 : ℤ)}) :=
    (Ideal.liesOver_span_iff w.1.isPrime.ne_top
      (Nat.prime_iff_prime_int.mp Nat.prime_three)).mpr (by simpa using hw)
  have hram := NumberField.count_normalizedFactors_span_prime_eq_ramificationIdx L
    w.1.asIdeal 3 Nat.prime_three
  norm_num only [Nat.cast_ofNat] at hram
  rw [hcount, hram] at h3
  exact congrArg₂ (fun a b : ℕ ↦ (a : ℚ) / b) hn h3

end ThreeAdicPlan
