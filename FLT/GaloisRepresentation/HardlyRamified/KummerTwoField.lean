/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.FieldTheory.SplittingField.IsSplittingField
public import Mathlib.Algebra.CubicDiscriminant
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# The splitting field of the Kummer polynomial for two

The field `K₀` is the splitting field of `X ^ 3 - 2` over the rationals. Its degree is six,
three has a unique prime above it with residue field `ZMod 3`, and every prime above two has
ramification index three.

The local computations use principal-ideal powers and the ramification–inertia degree formula.
For an integral cube root `a` of two, `(a + 1)^3 = 3 * (a^2 + a + 1)`, where the second factor is
a unit. The square root of minus three supplies the quadratic ramification at three. An integral
root of `X^2 + X + 1` rules out residue degree one at two.
-/

@[expose] public section

noncomputable section

namespace ThreeAdicPlan

open Polynomial NumberField

/-- The polynomial defining the Kummer extension for two at the prime three. -/
def kummerTwoPolynomial : ℚ[X] := X ^ 3 - C 2

/-- The point field of the Kummer object for two: `ℚ(ζ₃, ∛2)`. -/
abbrev K₀ := kummerTwoPolynomial.SplittingField

instance : NumberField K₀ where
  to_finiteDimensional := inferInstance

/-- The Kummer polynomial has degree three. -/
@[simp] theorem kummerTwoPolynomial_natDegree : kummerTwoPolynomial.natDegree = 3 := by
  simp [kummerTwoPolynomial]

/-- Eisenstein's criterion at two for the integral Kummer polynomial. -/
theorem kummerTwoPolynomial_isEisensteinAt :
    (X ^ 3 - C 2 : ℤ[X]).IsEisensteinAt (Ideal.span {(2 : ℤ)}) := by
  apply (monic_X_pow_sub_C (2 : ℤ) (by decide : 3 ≠ 0)).isEisensteinAt_of_mem_of_notMem
  · exact ((Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).mpr Int.prime_two).ne_top
  · intro n hn
    simp only [natDegree_X_pow_sub_C] at hn
    interval_cases n <;> norm_num [coeff_sub, coeff_X_pow, coeff_C, Ideal.mem_span_singleton]
  · norm_num [coeff_sub, coeff_X_pow, coeff_C, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]

/-- The Kummer polynomial is irreducible over the rationals. -/
theorem kummerTwoPolynomial_irreducible : Irreducible kummerTwoPolynomial := by
  have hm := monic_X_pow_sub_C (2 : ℤ) (by decide : 3 ≠ 0)
  have hi := kummerTwoPolynomial_isEisensteinAt.irreducible
    ((Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).mpr Int.prime_two) hm.isPrimitive
    (by rw [natDegree_X_pow_sub_C]; decide)
  convert (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    hm.isPrimitive).mp hi using 1
  norm_num [kummerTwoPolynomial]
  exact map_ofNat C 2

instance kummerTwoField_isGalois : IsGalois ℚ K₀ :=
  IsGalois.of_separable_splitting_field kummerTwoPolynomial_irreducible.separable

/-- The cubic degree divides the degree of its splitting field. -/
theorem three_dvd_finrank_kummerTwoField : 3 ∣ Module.finrank ℚ K₀ := by
  simpa using kummerTwoPolynomial_irreducible.natDegree_dvd_finrank
    (IsSplittingField.splits K₀ kummerTwoPolynomial)

/-- The degree of the splitting field is at most six. -/
theorem finrank_kummerTwoField_le_six : Module.finrank ℚ K₀ ≤ 6 := by
  simpa [Nat.factorial] using IsSplittingField.finrank_le_factorial (K := K₀) kummerTwoPolynomial

/-- The square root of the cubic discriminant belongs to its splitting field. -/
theorem exists_discriminant_sqrt_kummerTwoField : ∃ d : K₀, d ^ 2 = -108 := by
  let c : Cubic ℚ := ⟨1, 0, 0, -2⟩
  have hc : c.toPoly = kummerTwoPolynomial := by
    simp [c, Cubic.toPoly, kummerTwoPolynomial, sub_eq_add_neg]
  obtain ⟨x, y, z, hxyz⟩ := (Cubic.splits_iff_roots_eq_three
    (P := c) (φ := algebraMap ℚ K₀) (by norm_num [c])).mp
      (by rw [hc]; exact IsSplittingField.splits K₀ kummerTwoPolynomial)
  refine ⟨(x - y) * (x - z) * (y - z), ?_⟩
  have hd := Cubic.discr_eq_prod_three_roots (P := c)
    (φ := algebraMap ℚ K₀) (by norm_num [c]) hxyz
  norm_num [c, Cubic.discr] at hd
  exact hd.symm

/-- The quadratic discriminant factor is irreducible over the rationals. -/
theorem kummerTwoDiscriminantPolynomial_irreducible :
    Irreducible (X ^ 2 - C (-108) : ℚ[X]) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · norm_num [degree_X_pow_sub_C]
  · intro x hx
    simp only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_C] at hx
    nlinarith [sq_nonneg x]

/-- The quadratic discriminant field forces even splitting-field degree. -/
theorem two_dvd_finrank_kummerTwoField : 2 ∣ Module.finrank ℚ K₀ := by
  obtain ⟨d, hd⟩ := exists_discriminant_sqrt_kummerTwoField
  have he : aeval d (X ^ 2 - C (-108) : ℚ[X]) = 0 := by simp [hd]
  have hm := minpoly.eq_of_irreducible_of_monic
    kummerTwoDiscriminantPolynomial_irreducible he
    (monic_X_pow_sub_C (-108 : ℚ) (by decide : 2 ≠ 0))
  have hi : IsIntegral ℚ d := ⟨_, monic_X_pow_sub_C (-108 : ℚ) (by decide), he⟩
  simpa [← hm] using minpoly.degree_dvd hi

/-- The point field of the Kummer object for two is sextic. -/
theorem finrank_kummerTwoField : Module.finrank ℚ K₀ = 6 := by
  have h2 := two_dvd_finrank_kummerTwoField
  have h3 := three_dvd_finrank_kummerTwoField
  have hle := finrank_kummerTwoField_le_six
  have hpos := Module.finrank_pos (R := ℚ) (M := K₀)
  omega

/-- An integral cube root of two in the splitting field. -/
theorem exists_integral_cubeRoot_two : ∃ a : 𝓞 K₀, a ^ 3 = 2 := by
  obtain ⟨a, ha⟩ := (IsSplittingField.splits K₀ kummerTwoPolynomial).exists_eval_eq_zero
    (by rw [degree_map]; exact degree_ne_of_natDegree_ne (by simp))
  have ha' : a ^ 3 = 2 := by
    simpa [kummerTwoPolynomial, sub_eq_zero] using ha
  have hi : IsIntegral ℤ a := ⟨X ^ 3 - C 2,
    monic_X_pow_sub_C (2 : ℤ) (by decide), by simp [ha']⟩
  refine ⟨⟨a, hi⟩, ?_⟩
  apply RingOfIntegers.ext
  change a ^ 3 = 2
  exact ha'

/-- An integral square root of minus three in the splitting field. -/
theorem exists_integral_sqrt_neg_three : ∃ b : 𝓞 K₀, b ^ 2 = -3 := by
  obtain ⟨d, hd⟩ := exists_discriminant_sqrt_kummerTwoField
  have hb : (d / 6) ^ 2 = -3 := by rw [div_pow, hd]; norm_num
  have hi : IsIntegral ℤ (d / 6) := ⟨X ^ 2 - C (-3),
    monic_X_pow_sub_C (-3 : ℤ) (by decide), by simp [hb]⟩
  refine ⟨⟨d / 6, hi⟩, ?_⟩
  apply RingOfIntegers.ext
  change (d / 6) ^ 2 = -3
  exact hb

/-- The ideal generated by two is a cube. -/
theorem span_two_eq_cube : ∃ I : Ideal (𝓞 K₀), Ideal.span {(2 : 𝓞 K₀)} = I ^ 3 := by
  obtain ⟨a, ha⟩ := exists_integral_cubeRoot_two
  exact ⟨Ideal.span {a}, by rw [Ideal.span_singleton_pow, ha]⟩

/-- The ideal generated by three is a square. -/
theorem span_three_eq_square : ∃ I : Ideal (𝓞 K₀), Ideal.span {(3 : 𝓞 K₀)} = I ^ 2 := by
  obtain ⟨b, hb⟩ := exists_integral_sqrt_neg_three
  exact ⟨Ideal.span {b}, by rw [Ideal.span_singleton_pow, hb, Ideal.span_singleton_neg]⟩

/-- The ideal generated by three is a cube: `(∛2 + 1)^3` is three times a unit. -/
theorem span_three_eq_cube : ∃ I : Ideal (𝓞 K₀), Ideal.span {(3 : 𝓞 K₀)} = I ^ 3 := by
  obtain ⟨a, ha⟩ := exists_integral_cubeRoot_two
  have hu : IsUnit (a ^ 2 + a + 1) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨a - 1, ?_⟩
    calc
      (a ^ 2 + a + 1) * (a - 1) = a ^ 3 - 1 := by ring
      _ = 1 := by rw [ha]; norm_num
  refine ⟨Ideal.span {a + 1}, ?_⟩
  have hpow : (a + 1) ^ 3 = 3 * (a ^ 2 + a + 1) := by
    calc
      (a + 1) ^ 3 = a ^ 3 + 3 * a ^ 2 + 3 * a + 1 := by ring
      _ = 3 * (a ^ 2 + a + 1) := by rw [ha]; ring
  rw [Ideal.span_singleton_pow, hpow, ← Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_eq_top.mpr hu, Ideal.mul_top]

/-- An ideal power decomposition forces divisibility of every ramification index above it. -/
theorem dvd_ramificationIdx_of_span_eq_pow {p : ℤ} (hp : p ≠ 0)
    (P : Ideal (𝓞 K₀)) [P.LiesOver (Ideal.span {p})] {n : ℕ}
    (h : ∃ I : Ideal (𝓞 K₀), Ideal.span {(p : 𝓞 K₀)} = I ^ n) :
    n ∣ P.ramificationIdx ℤ := by
  classical
  have hmap : (Ideal.span {p}).map (algebraMap ℤ (𝓞 K₀)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot (by simpa [Ideal.span_singleton_eq_bot] using hp)
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
    (Ideal.span {p}) P hmap]
  obtain ⟨I, hI⟩ := h
  rw [Ideal.map_span, Set.image_singleton]
  change n ∣ (UniqueFactorizationMonoid.normalizedFactors
    (Ideal.span {(p : 𝓞 K₀)})).count P
  rw [hI, UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul]
  exact Nat.dvd_mul_right _ _

/-- Each prime above three has ramification index divisible by six. -/
theorem six_dvd_ramificationIdx_at_three (P : Ideal (𝓞 K₀))
    [P.LiesOver (Ideal.span {(3 : ℤ)})] : 6 ∣ P.ramificationIdx ℤ := by
  have h2 := dvd_ramificationIdx_of_span_eq_pow (by norm_num : (3 : ℤ) ≠ 0)
    P span_three_eq_square
  have h3 := dvd_ramificationIdx_of_span_eq_pow (by norm_num : (3 : ℤ) ≠ 0)
    P span_three_eq_cube
  omega

/-- The contribution of any prime to the degree formula is at most six. -/
theorem ramificationIdx_mul_inertiaDeg_le_six (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 K₀)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    P.ramificationIdx ℤ * P.inertiaDeg ℤ ≤ 6 := by
  classical
  let q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K₀) := ⟨P, ‹_›, ‹_›⟩
  have h := Finset.single_le_sum
    (f := fun q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K₀) ↦
      q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ)
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ q)
  simpa only [Ideal.sum_ramification_inertia_eq_finrank, RingOfIntegers.rank,
    finrank_kummerTwoField] using h

/-- Three is totally ramified and has inertia degree one. -/
theorem ramification_inertia_at_three (P : Ideal (𝓞 K₀)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(3 : ℤ)})] :
    P.ramificationIdx ℤ = 6 ∧ P.inertiaDeg ℤ = 1 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have : (Ideal.span {(3 : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 3
  have hd := six_dvd_ramificationIdx_at_three P
  have he := P.ramificationIdx_pos ℤ
  have hf := P.inertiaDeg_pos ℤ
  have h := ramificationIdx_mul_inertiaDeg_le_six 3 P
  have hle : P.ramificationIdx ℤ ≤ 6 := by nlinarith
  have heq : P.ramificationIdx ℤ = 6 := by omega
  constructor
  · exact heq
  · rw [heq] at h
    omega

/-- The specified prime above three in any number field. -/
def primeAboveThree (K : Type*) [Field K] [NumberField K] : Ideal (𝓞 K) := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have : (Ideal.span {(3 : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 3
  exact (Classical.choice (inferInstance :
    Nonempty ((Ideal.span {(3 : ℤ)}).primesOver (𝓞 K)))).1

instance primeAboveThree_isPrime (K : Type*) [Field K] [NumberField K] :
    (primeAboveThree K).IsPrime := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have : (Ideal.span {(3 : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 3
  exact (Classical.choice (inferInstance :
    Nonempty ((Ideal.span {(3 : ℤ)}).primesOver (𝓞 K)))).2.1

instance primeAboveThree_liesOver (K : Type*) [Field K] [NumberField K] :
    (primeAboveThree K).LiesOver (Ideal.span {(3 : ℤ)}) := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have : (Ideal.span {(3 : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 3
  exact (Classical.choice (inferInstance :
    Nonempty ((Ideal.span {(3 : ℤ)}).primesOver (𝓞 K)))).2.2

instance primeAboveThree_isMaximal (K : Type*) [Field K] [NumberField K] :
    (primeAboveThree K).IsMaximal := by
  have : (Ideal.span {(3 : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 3
  exact Ideal.IsMaximal.of_liesOver_isMaximal (primeAboveThree K) (Ideal.span {(3 : ℤ)})

/-- The only prime above three is the specified `primeAboveThree K`. -/
def UniquePrimeAboveThree (K : Type*) [Field K] [NumberField K] : Prop :=
  (Ideal.span {(3 : ℤ)}).primesOver (𝓞 K) = {primeAboveThree K}

/-- The residue field at the specified prime above three is the prime field. -/
def ResidueFieldAtThreeIsF3 (K : Type*) [Field K] [NumberField K] : Prop :=
  Nonempty ((𝓞 K ⧸ primeAboveThree K) ≃+* ZMod 3)

/-- There is exactly one prime of the Kummer field above three. -/
theorem uniquePrimeAboveThree_kummerTwoField : UniquePrimeAboveThree K₀ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have : (Ideal.span {(3 : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 3
  have hsum := Ideal.sum_ramification_inertia_eq_finrank
    (Ideal.span {(3 : ℤ)}) (𝓞 K₀)
  have hall : ∀ q : (Ideal.span {(3 : ℤ)}).primesOver (𝓞 K₀),
      q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = 6 := by
    intro q
    obtain ⟨he, hf⟩ := ramification_inertia_at_three q.1
    rw [he, hf, mul_one]
  simp only [hall, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    RingOfIntegers.rank, finrank_kummerTwoField] at hsum
  have hcard : Fintype.card ((Ideal.span {(3 : ℤ)}).primesOver (𝓞 K₀)) = 1 := by omega
  have : Subsingleton ((Ideal.span {(3 : ℤ)}).primesOver (𝓞 K₀)) :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨⟨inferInstance, inferInstance⟩, ?_⟩
  intro P hP
  exact congrArg Subtype.val (Subsingleton.elim
    (⟨P, hP⟩ : (Ideal.span {(3 : ℤ)}).primesOver (𝓞 K₀))
    ⟨primeAboveThree K₀, inferInstance, inferInstance⟩)

/-- The specified prime above three has residue field with three elements. -/
theorem residueFieldAtThreeIsF3_kummerTwoField : ResidueFieldAtThreeIsF3 K₀ := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have : (Ideal.span {(3 : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 3
  have : Infinite (𝓞 K₀) := Infinite.of_injective (fun n : ℕ ↦ (n : 𝓞 K₀))
    Nat.cast_injective
  have h : 3 ^ (primeAboveThree K₀).inertiaDeg ℤ = Ideal.absNorm (primeAboveThree K₀) :=
    Ideal.natAbs_pow_inertiaDeg (3 : ℤ) (primeAboveThree K₀)
  rw [(ramification_inertia_at_three (primeAboveThree K₀)).2, pow_one] at h
  have hc : Nat.card (𝓞 K₀ ⧸ primeAboveThree K₀) = 3 := h.symm
  have : Finite (𝓞 K₀ ⧸ primeAboveThree K₀) :=
    Nat.finite_of_card_ne_zero (by omega)
  let := Fintype.ofFinite (𝓞 K₀ ⧸ primeAboveThree K₀)
  refine ⟨(ZMod.ringEquivOfPrime (𝓞 K₀ ⧸ primeAboveThree K₀) (by decide) ?_).symm⟩
  simpa only [Nat.card_eq_fintype_card] using hc

/-- An integral root of the third cyclotomic polynomial in the Kummer field. -/
theorem exists_integral_thirdRoot : ∃ z : 𝓞 K₀, z ^ 2 + z + 1 = 0 := by
  obtain ⟨b, hb⟩ := exists_integral_sqrt_neg_three
  have hb' : (b : K₀) ^ 2 = -3 := by
    have := congrArg (algebraMap (𝓞 K₀) K₀) hb
    simpa only [map_pow, map_neg, map_ofNat] using this
  let z : K₀ := ((b : K₀) - 1) / 2
  have hz : z ^ 2 + z + 1 = 0 := by
    dsimp [z]
    field_simp
    linear_combination hb'
  have hm : (X ^ 2 + X + 1 : ℤ[X]).Monic := by
    simpa only [add_assoc] using
      (monic_X_pow_add (R := ℤ) (n := 2) (p := X + 1) (by compute_degree; norm_num))
  have hi : IsIntegral ℤ z := ⟨X ^ 2 + X + 1, hm, by simpa using hz⟩
  refine ⟨⟨z, hi⟩, ?_⟩
  apply RingOfIntegers.ext
  change z ^ 2 + z + 1 = 0
  exact hz

/-- A prime above two cannot have residue degree one, since the third cyclotomic
polynomial has no root in `𝔽₂`. -/
theorem inertiaDeg_at_two_ne_one (P : Ideal (𝓞 K₀)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(2 : ℤ)})] : P.inertiaDeg ℤ ≠ 1 := by
  intro hf
  have : Infinite (𝓞 K₀) := Infinite.of_injective (fun n : ℕ ↦ (n : 𝓞 K₀))
    Nat.cast_injective
  have hcard : 2 ^ P.inertiaDeg ℤ = Ideal.absNorm P :=
    Ideal.natAbs_pow_inertiaDeg (2 : ℤ) P
  rw [hf, pow_one] at hcard
  have hc : Nat.card (𝓞 K₀ ⧸ P) = 2 := hcard.symm
  have : Finite (𝓞 K₀ ⧸ P) := Nat.finite_of_card_ne_zero (by omega)
  let := Fintype.ofFinite (𝓞 K₀ ⧸ P)
  let e : (𝓞 K₀ ⧸ P) ≃+* ZMod 2 :=
    (ZMod.ringEquivOfPrime (𝓞 K₀ ⧸ P) Nat.prime_two
      (by simpa only [Nat.card_eq_fintype_card] using hc)).symm
  obtain ⟨z, hz⟩ := exists_integral_thirdRoot
  have he := congrArg (e.toRingHom.comp (Ideal.Quotient.mk P)) hz
  simp only [map_add, map_pow, map_one, map_zero] at he
  have hn : ∀ x : ZMod 2, x ^ 2 + x + 1 ≠ 0 := by decide
  exact hn _ he

/-- Each prime above two has ramification index three and residue degree two. -/
theorem ramification_inertia_at_two (P : Ideal (𝓞 K₀)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(2 : ℤ)})] :
    P.ramificationIdx ℤ = 3 ∧ P.inertiaDeg ℤ = 2 := by
  have hd := dvd_ramificationIdx_of_span_eq_pow (by norm_num : (2 : ℤ) ≠ 0)
    P span_two_eq_cube
  have he := P.ramificationIdx_pos ℤ
  have hf := P.inertiaDeg_pos ℤ
  have hf1 := inertiaDeg_at_two_ne_one P
  have h := ramificationIdx_mul_inertiaDeg_le_six 2 P
  have he3 : 3 ≤ P.ramificationIdx ℤ := Nat.le_of_dvd he hd
  have hf2 : 2 ≤ P.inertiaDeg ℤ := by omega
  constructor <;> nlinarith

/-- The ramification index at two in the sextic Kummer field is three. -/
theorem ramificationIdx_at_two (P : Ideal (𝓞 K₀)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(2 : ℤ)})] : P.ramificationIdx ℤ = 3 :=
  (ramification_inertia_at_two P).1

/-- The class-number-independent arithmetic data for the sextic Kummer field. -/
theorem kummer_two_field_data_without_classNumber :
    Module.finrank ℚ K₀ = 6 ∧ UniquePrimeAboveThree K₀ ∧ ResidueFieldAtThreeIsF3 K₀ ∧
      ∀ (P : Ideal (𝓞 K₀)) [P.IsPrime] [P.LiesOver (Ideal.span {(2 : ℤ)})],
        P.ramificationIdx ℤ = 3 :=
  ⟨finrank_kummerTwoField, uniquePrimeAboveThree_kummerTwoField,
    residueFieldAtThreeIsF3_kummerTwoField, ramificationIdx_at_two⟩

end ThreeAdicPlan
