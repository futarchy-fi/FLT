/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.KummerTwoClassNumber
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.NumberTheory.RamificationInertia.Ramification

/-!
# Quadratic Kummer reduction over the sextic field

The reduction uses class number one and parity of prime-ideal multiplicities.
The parity argument applies also at residue characteristic two.

`kummer_two_quadratic_reduction` supplies the square-root generator with radicand
`u * π ^ a`, where `a < 2`. `KummerTwoDyadicSquareClassCheck` states the remaining
local calculation; it is a proposition definition, not an assumed theorem.
-/

@[expose] public section

noncomputable section

namespace ThreeAdicPlan

open NumberField Polynomial IntermediateField UniqueFactorizationMonoid

/-- Every quadratic extension in characteristic zero has a square-root generator. -/
theorem exists_quadratic_kummer_generator (K L : Type*) [Field K] [CharZero K]
    [Field L] [Algebra K L] [FiniteDimensional K L] (hdegree : Module.finrank K L = 2) :
    ∃ (α : K) (x : L), x ^ 2 = algebraMap K L α ∧ K⟮x⟯ = ⊤ ∧
      Irreducible (X ^ 2 - C α) := by
  let : Algebra.IsQuadraticExtension K L := ⟨hdegree⟩
  have hroots : (primitiveRoots (Module.finrank K L) K).Nonempty := by
    rw [hdegree]
    exact ⟨-1, (mem_primitiveRoots (by decide)).mpr (IsPrimitiveRoot.neg_one 0 (by decide))⟩
  obtain ⟨x, ⟨α, hα⟩, hx⟩ := exists_root_adjoin_eq_top_of_isCyclic K L hroots
  refine ⟨α, x, ?_, hx, ?_⟩
  · simpa only [hdegree] using hα.symm
  · simpa only [hdegree] using irreducible_X_pow_sub_C_of_root_adjoin_eq_top hα.symm hx

/-- Class number one makes every ideal of the sextic field principal. -/
theorem kummerTwoField_isPrincipalIdealRing : IsPrincipalIdealRing (𝓞 K₀) :=
  classNumber_eq_one_iff.mp classNumber_kummerTwoField

/-- A generator of the unique prime above three exists. -/
theorem exists_generator_primeAboveThree :
    ∃ π : 𝓞 K₀, Ideal.span {π} = primeAboveThree K₀ := by
  let := kummerTwoField_isPrincipalIdealRing
  exact ⟨Submodule.IsPrincipal.generator (primeAboveThree K₀),
    Ideal.span_singleton_generator _⟩

/-- For an integral square root, twice the upstairs valuation is the downstairs
valuation multiplied by the ramification index. No residue-characteristic restriction is needed. -/
theorem quadratic_ramification_count (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (Q : Ideal (𝓞 K)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver Q]
    (α : 𝓞 K) (hα : α ≠ 0) (x : 𝓞 L)
    (hx : x ^ 2 = algebraMap (𝓞 K) (𝓞 L) α) :
    P.ramificationIdx (𝓞 K) * (normalizedFactors (Ideal.span {α})).count Q =
      2 * (normalizedFactors (Ideal.span {x})).count P := by
  classical
  have hP : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hQ P
  have hαI : Ideal.span {α} ≠ ⊥ := by simpa using hα
  have hx0 : x ≠ 0 := by
    intro h
    have := hx
    simp [h] at this
    exact hα ((map_eq_zero_iff _ (RingOfIntegers.algebraMap.injective K L)).mp this.symm)
  have hxI : Ideal.span {x} ≠ ⊥ := by simpa using hx0
  have hm := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul
    hαI (Ideal.prime_of_isPrime hQ inferInstance).irreducible
    (Ideal.prime_of_isPrime hP inferInstance).irreducible hP
  rw [Ideal.map_span, Set.image_singleton, ← hx, ← Ideal.span_singleton_pow,
    emultiplicity_eq_count_normalizedFactors
      (Ideal.prime_of_isPrime hP inferInstance).irreducible (pow_ne_zero 2 hxI),
    emultiplicity_eq_count_normalizedFactors
      (Ideal.prime_of_isPrime hQ inferInstance).irreducible hαI,
    normalize_eq, normalize_eq, normalizedFactors_pow, Multiset.count_nsmul,
    Ideal.ramificationIdx'_eq_ramificationIdx Q P hQ] at hm
  exact_mod_cast hm.symm

/-- An unramified prime has even valuation on an integral quadratic radicand,
including primes above two. -/
theorem even_count_of_unramified_square_root (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (Q : Ideal (𝓞 K)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver Q]
    [Algebra.IsUnramifiedAt (𝓞 K) P]
    (α : 𝓞 K) (hα : α ≠ 0) (x : 𝓞 L)
    (hx : x ^ 2 = algebraMap (𝓞 K) (𝓞 L) α) :
    Even ((normalizedFactors (Ideal.span {α})).count Q) := by
  have h := quadratic_ramification_count K L Q hQ P α hα x hx
  rw [Ideal.ramificationIdx_eq_one P (𝓞 K), one_mul] at h
  exact even_iff_two_dvd.mpr ⟨_, h⟩

/-- Odd valuation forces ramification even in residue characteristic two. -/
theorem ramified_of_odd_count_square_root (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (Q : Ideal (𝓞 K)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver Q]
    (α : 𝓞 K) (hα : α ≠ 0) (x : 𝓞 L)
    (hx : x ^ 2 = algebraMap (𝓞 K) (𝓞 L) α)
    (hodd : Odd ((normalizedFactors (Ideal.span {α})).count Q)) :
    ¬ Algebra.IsUnramifiedAt (𝓞 K) P := by
  intro hur
  let := hur
  exact (Nat.not_even_iff_odd.mpr hodd)
    (even_count_of_unramified_square_root K L Q hQ P α hα x hx)

/-- In a multiset with even counts away from one distinguished element, removing
zero or one copy of that element leaves twice a multiset. -/
theorem multiset_eq_singleton_mod_two {A : Type*} [DecidableEq A]
    (s : Multiset A) (q : A) (h : ∀ p, p ≠ q → Even (s.count p)) :
    ∃ (a : ℕ) (t : Multiset A), a < 2 ∧ s = Multiset.replicate a q + 2 • t := by
  by_cases hq : Even (s.count q)
  · obtain ⟨t, ht⟩ := Multiset.exists_smul_of_dvd_count s (k := 2) (by
      intro p _
      by_cases hp : p = q
      · simpa [hp] using even_iff_two_dvd.mp hq
      · exact even_iff_two_dvd.mp (h p hp))
    exact ⟨0, t, by decide, by simpa using ht⟩
  · have hpos : 0 < s.count q := by
      by_contra hn
      have : s.count q = 0 := by omega
      simp [this] at hq
    obtain ⟨t, ht⟩ := Multiset.exists_smul_of_dvd_count (s.erase q) (k := 2) (by
      intro p _
      by_cases hp : p = q
      · subst p
        rw [Multiset.count_erase_self]
        have hodd := Nat.not_even_iff_odd.mp hq
        obtain ⟨n, hn⟩ := hodd
        exact ⟨n, by omega⟩
      · rw [Multiset.count_erase_of_ne hp]
        exact even_iff_two_dvd.mp (h p hp))
    refine ⟨1, t, by decide, ?_⟩
    rw [← ht]
    simpa only [Multiset.replicate_one, Multiset.singleton_add] using
      (Multiset.cons_erase (Multiset.count_pos.mp hpos)).symm

/-- Even ideal multiplicities outside one prime leave a square ideal and at most
one copy of that prime. -/
theorem ideal_eq_prime_pow_mul_sq (I Q : Ideal (𝓞 K₀)) (hI : I ≠ ⊥)
    (heven : ∀ P : Ideal (𝓞 K₀), P.IsPrime → P ≠ ⊥ → P ≠ Q →
      Even ((normalizedFactors I).count P)) :
    ∃ (a : ℕ) (J : Ideal (𝓞 K₀)), a < 2 ∧ I = Q ^ a * J ^ 2 := by
  classical
  obtain ⟨a, t, ha, ht⟩ := multiset_eq_singleton_mod_two (normalizedFactors I) Q (by
    intro P hPQ
    by_cases hp : P ∈ normalizedFactors I
    · have hp' := prime_of_normalized_factor P hp
      exact heven P (Ideal.isPrime_of_prime hp') hp'.ne_zero hPQ
    · simp [Multiset.count_eq_zero.mpr hp])
  refine ⟨a, t.prod, ha, ?_⟩
  calc
    I = (normalizedFactors I).prod := (associated_iff_eq.mp (prod_normalizedFactors hI)).symm
    _ = Q ^ a * t.prod ^ 2 := by rw [ht, Multiset.prod_add, Multiset.prod_replicate,
      Multiset.prod_nsmul]

/-- Class number one turns the ideal square factor into the square of an element.
Thus every integral radicand with even valuations away from three has the required shape. -/
theorem radicand_eq_unit_mul_prime_pow_mul_sq (α : 𝓞 K₀) (hα : α ≠ 0)
    (π : 𝓞 K₀) (hπ : Ideal.span {π} = primeAboveThree K₀)
    (heven : ∀ Q : Ideal (𝓞 K₀), Q.IsPrime → Q ≠ ⊥ → Q ≠ primeAboveThree K₀ →
      Even ((normalizedFactors (Ideal.span {α})).count Q)) :
    ∃ (u : (𝓞 K₀)ˣ) (a : ℕ) (b : 𝓞 K₀), a < 2 ∧ b ≠ 0 ∧
      α = u * π ^ a * b ^ 2 := by
  let := kummerTwoField_isPrincipalIdealRing
  obtain ⟨a, J, ha, hJ⟩ := ideal_eq_prime_pow_mul_sq (Ideal.span {α}) (primeAboveThree K₀)
    (by simpa using hα) heven
  obtain ⟨b, hb⟩ := (inferInstance : J.IsPrincipal).principal
  have heq : Ideal.span {α} = Ideal.span {π ^ a * b ^ 2} := by
    rw [hJ, ← hπ, hb, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
      Ideal.span_singleton_mul_span_singleton]
  obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_span_singleton.mp heq).symm
  refine ⟨u, a, b, ha, ?_, ?_⟩
  · intro hb0
    simp [hb0] at hu
    exact hα hu.symm
  · rw [← hu]
    ring

/-- Clearing denominators in a quadratic generator gives a nonzero integral radicand
and an integral square root generating the same field. -/
@[nolint unusedArguments]
theorem exists_integral_quadratic_kummer_generator (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (hdegree : Module.finrank K L = 2) :
    ∃ (α : 𝓞 K) (x : 𝓞 L), α ≠ 0 ∧
      x ^ 2 = algebraMap (𝓞 K) (𝓞 L) α ∧ K⟮(x : L)⟯ = ⊤ := by
  obtain ⟨α, x, hx, hgen, hirr⟩ := exists_quadratic_kummer_generator K L hdegree
  have hα : α ≠ 0 := ne_zero_of_irreducible_X_pow_sub_C' (by decide : 2 ≠ 1) hirr
  obtain ⟨c, d, hd, hcd⟩ := IsFractionRing.div_surjective (𝓞 K) α
  have hd0 : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
  have hdK : (d : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd0
  have hcK : (c : K) ≠ 0 := by
    intro hc
    simp [hc] at hcd
    exact hα hcd.symm
  let y := x * algebraMap K L (d : K)
  have hy : y ^ 2 = algebraMap K L ((c * d : 𝓞 K) : K) := by
    dsimp [y]
    rw [mul_pow, hx, ← map_pow, ← map_mul]
    congr 1
    rw [← hcd]
    push_cast
    field_simp
  have hyint : IsIntegral ℤ y := by
    apply IsIntegral.of_pow (n := 2) (by decide)
    rw [hy]
    exact isIntegral_algebraMap_iff.mpr (RingOfIntegers.isIntegral_coe (c * d))
  refine ⟨c * d, ⟨y, hyint⟩, ?_, ?_, ?_⟩
  · exact mul_ne_zero (RingOfIntegers.coe_ne_zero_iff.mp hcK) hd0
  · apply RingOfIntegers.ext
    exact hy
  · exact (adjoin_simple_mul_algebraMap x (d : K) hdK).trans hgen

/-- All finite primes of an extension of the sextic field, except the unique prime
above three, are unramified. -/
@[nolint unusedArguments]
def KummerTwoUnramifiedOutsideThree (L : Type*) [Field L] [NumberField L] [Algebra K₀ L] : Prop :=
  ∀ (Q : Ideal (𝓞 K₀)) [Q.IsPrime], Q ≠ ⊥ → Q ≠ primeAboveThree K₀ →
    ∀ (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver Q], Algebra.IsUnramifiedAt (𝓞 K₀) P

/-- The unramified hypothesis supplies every parity condition needed in the global
ideal factorization, including those at primes above two. -/
theorem even_count_outside_three (L : Type*) [Field L] [NumberField L] [Algebra K₀ L]
    (hur : KummerTwoUnramifiedOutsideThree L)
    (α : 𝓞 K₀) (hα : α ≠ 0) (x : 𝓞 L)
    (hx : x ^ 2 = algebraMap (𝓞 K₀) (𝓞 L) α)
    (Q : Ideal (𝓞 K₀)) (hQprime : Q.IsPrime) (hQ : Q ≠ ⊥)
    (hQthree : Q ≠ primeAboveThree K₀) :
    Even ((normalizedFactors (Ideal.span {α})).count Q) := by
  let := hQprime
  let : Q.IsMaximal := hQprime.isMaximal hQ
  obtain ⟨P, hPprime, hPQ⟩ := (inferInstance : Nonempty (Q.primesOver (𝓞 L)))
  let := hPprime
  let := hPQ
  let := hur Q hQ hQthree P
  exact even_count_of_unramified_square_root K₀ L Q hQ P α hα x hx

/-- The quadratic Kummer reduction: a quadratic extension unramified away from three
is generated by the square root of a unit times the zeroth or first power of a generator
of the prime above three. -/
theorem kummer_two_quadratic_reduction (L : Type*) [Field L] [NumberField L]
    [Algebra K₀ L] [FiniteDimensional K₀ L]
    (hdegree : Module.finrank K₀ L = 2) (hur : KummerTwoUnramifiedOutsideThree L) :
    ∃ (π : 𝓞 K₀) (u : (𝓞 K₀)ˣ) (a : ℕ) (y : L),
      Ideal.span {π} = primeAboveThree K₀ ∧ a < 2 ∧
      y ^ 2 = algebraMap K₀ L ((u * π ^ a : 𝓞 K₀) : K₀) ∧ K₀⟮y⟯ = ⊤ := by
  obtain ⟨α, x, hα, hx, hgen⟩ := exists_integral_quadratic_kummer_generator K₀ L hdegree
  obtain ⟨π, hπ⟩ := exists_generator_primeAboveThree
  obtain ⟨u, a, b, ha, hb, hfactor⟩ := radicand_eq_unit_mul_prime_pow_mul_sq α hα π hπ
    (even_count_outside_three L hur α hα x hx)
  have hbK : (b : K₀) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hb
  have hbL : algebraMap K₀ L (b : K₀) ≠ 0 := (map_ne_zero (algebraMap K₀ L)).mpr hbK
  let y := (x : L) / algebraMap K₀ L (b : K₀)
  refine ⟨π, u, a, y, hπ, ha, ?_, ?_⟩
  · have hxL : (x : L) ^ 2 = algebraMap K₀ L (α : K₀) :=
      congrArg (algebraMap (𝓞 L) L) hx
    dsimp [y]
    rw [div_pow, hxL, hfactor]
    push_cast
    field_simp
  · change K₀⟮(x : L) / algebraMap K₀ L (b : K₀)⟯ = ⊤
    rw [div_eq_mul_inv, ← map_inv₀, adjoin_simple_mul_algebraMap _ _ (inv_ne_zero hbK)]
    exact hgen

/-- The remaining, unproved dyadic square-class check for R7. Among the classes
`u * π ^ a`, with `a ∈ {0, 1}`, only a square can give a square-root extension
unramified at every prime above two. Modulo unit squares there are eight unit
classes (two fundamental units and `-1`), hence sixteen candidates after adjoining
the exponent of `π`. This definition quantifies over all unit representatives,
so it does not require a choice of fundamental units. Neither the enumeration of
representatives nor the dyadic calculation is asserted as a theorem here. -/
def KummerTwoDyadicSquareClassCheck : Prop :=
  ∀ (π : 𝓞 K₀), Ideal.span {π} = primeAboveThree K₀ →
    ∀ (u : (𝓞 K₀)ˣ) (a : ℕ), a < 2 →
      ∀ (L : Type*) [Field L] [NumberField L] [Algebra K₀ L] (y : L),
        y ^ 2 = algebraMap K₀ L ((u * π ^ a : 𝓞 K₀) : K₀) → K₀⟮y⟯ = ⊤ →
        (∀ (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(2 : ℤ)})],
          Algebra.IsUnramifiedAt (𝓞 K₀) P) →
        IsSquare ((u * π ^ a : 𝓞 K₀) : K₀)

end ThreeAdicPlan
