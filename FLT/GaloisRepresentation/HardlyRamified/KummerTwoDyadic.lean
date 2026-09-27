/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.KummerTwoQuadratic
public import FLT.GaloisRepresentation.HardlyRamified.KummerTwoUnitSquareClasses

/-!
# Explicit dyadic obstructions in the sextic Kummer field

We prove `kummerTwoDyadicSquareClassCheck` and `no_quadratic_extension_auxiliary`.
The local argument uses square defects of valuation one or three, with two of valuation three.
The sign and two cubic units are independent modulo squares by this calculation;
Dirichlet's theorem bounds the unit square-class group by eight, so they generate it.
A generator above three is obtained from `(2 * z + 1) / (a + 1)`.
-/

@[expose] public section

noncomputable section

namespace ThreeAdicPlan

open NumberField Polynomial IntermediateField UniqueFactorizationMonoid

/-- Ideal-power membership measured by prime-ideal multiplicity. -/
theorem mem_prime_pow_iff_count {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) (x : R) (hx : x ≠ 0) (n : ℕ) :
    x ∈ P ^ n ↔ n ≤ (normalizedFactors (Ideal.span {x})).count P := by
  classical
  rw [← Ideal.span_singleton_le_iff_mem, ← Ideal.dvd_iff_le,
    pow_dvd_iff_le_emultiplicity,
    emultiplicity_eq_count_normalizedFactors
      (Ideal.prime_of_isPrime hP inferInstance).irreducible (by simpa using hx),
    normalize_eq]
  exact_mod_cast Iff.rfl

/-- A square in the third power of a nonzero prime has its root in the second power. -/
theorem mem_sq_of_sq_mem_cube {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) (x : R) (hx : x ^ 2 ∈ P ^ 3) :
    x ∈ P ^ 2 := by
  classical
  by_cases hx0 : x = 0
  · simp [hx0]
  rw [mem_prime_pow_iff_count P hP x hx0]
  rw [mem_prime_pow_iff_count P hP (x ^ 2) (pow_ne_zero 2 hx0),
    ← Ideal.span_singleton_pow, normalizedFactors_pow, Multiset.count_nsmul] at hx
  omega

/-- An element of order one has no power in the next prime-ideal power. -/
theorem pow_notMem_prime_pow_succ {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) (a : R)
    (ha : a ∈ P) (ha2 : a ∉ P ^ 2) (n : ℕ) : a ^ n ∉ P ^ (n + 1) := by
  classical
  have ha0 : a ≠ 0 := by rintro rfl; exact ha2 (Ideal.zero_mem _)
  have h1 : 1 ≤ (normalizedFactors (Ideal.span {a})).count P :=
    (mem_prime_pow_iff_count P hP a ha0 1).mp (by simpa using ha)
  have h2 := (mem_prime_pow_iff_count P hP a ha0 2).not.mp ha2
  have heq : (normalizedFactors (Ideal.span {a})).count P = 1 := by omega
  rw [mem_prime_pow_iff_count P hP (a ^ n) (pow_ne_zero n ha0),
    ← Ideal.span_singleton_pow, normalizedFactors_pow, Multiset.count_nsmul, heq]
  omega

/-- A square defect of valuation one is incompatible with being a square when `2 ∈ P²`. -/
theorem not_isSquare_of_defect_one {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : Ideal R) [P.IsPrime] (a b c r : R)
    (ha : a ∈ P) (ha2 : a ∉ P ^ 2) (h2 : (2 : R) ∈ P ^ 2)
    (hc : c ∉ P) (hr : r - b ^ 2 = a * c) : ¬ IsSquare r := by
  rintro ⟨x, rfl⟩
  have hid : (x - b) ^ 2 + 2 * b * (x - b) = a * c := by
    linear_combination hr
  have h2P : (2 : R) ∈ P := Ideal.pow_le_self (by decide : 2 ≠ 0) h2
  have hδ : x - b ∈ P := by
    apply (inferInstance : P.IsPrime).mem_of_pow_mem 2
    have hm : 2 * b * (x - b) ∈ P := P.mul_mem_right _ (P.mul_mem_right _ h2P)
    have hh := P.sub_mem (P.mul_mem_right c ha) hm
    simpa only [← hid, add_sub_cancel_right] using hh
  have hprod : a * c ∈ P ^ 2 := by
    rw [← hid]
    exact (P ^ 2).add_mem (Ideal.pow_mem_pow hδ 2)
      ((P ^ 2).mul_mem_right _ ((P ^ 2).mul_mem_right _ h2))
  exact ha2 ((Ideal.IsPrime.mem_pow_mul P hprod).resolve_right hc)

/-- A square defect of valuation three is incompatible with being a square when `2 ∈ P³`. -/
theorem not_isSquare_of_defect_three {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) (a b c r : R)
    (ha : a ∈ P) (ha2 : a ∉ P ^ 2) (h2 : (2 : R) ∈ P ^ 3)
    (hc : c ∉ P) (hr : r - b ^ 2 = a ^ 3 * c) : ¬ IsSquare r := by
  rintro ⟨x, rfl⟩
  have hid : (x - b) ^ 2 + 2 * b * (x - b) = a ^ 3 * c := by
    linear_combination hr
  have hδ3 : (x - b) ^ 2 ∈ P ^ 3 := by
    have hh := (P ^ 3).sub_mem ((P ^ 3).mul_mem_right c (Ideal.pow_mem_pow ha 3))
      ((P ^ 3).mul_mem_right (x - b) ((P ^ 3).mul_mem_right b h2))
    simpa only [← hid, add_sub_cancel_right] using hh
  have hδ2 := mem_sq_of_sq_mem_cube P hP (x - b) hδ3
  have hδ : x - b ∈ P := Ideal.pow_le_self (by decide : 2 ≠ 0) hδ2
  have hprod : a ^ 3 * c ∈ P ^ 4 := by
    rw [← hid]
    apply (P ^ 4).add_mem
    · simpa only [← pow_mul] using Ideal.pow_mem_pow hδ2 2
    · have hh := Ideal.mul_mem_mul ((P ^ 3).mul_mem_right b h2) hδ
      simpa only [← pow_succ] using hh
  exact pow_notMem_prime_pow_succ P hP a ha ha2 3
    ((Ideal.IsPrime.mem_pow_mul P hprod).resolve_right hc)

/-- Convenient representatives: the inverse cubic units and a radicand in the
square class of a generator above three. -/
def kummerTwoSquareClassRepresentative {R : Type*} [CommRing R]
    (a z : R) (s t u v : Fin 2) : R :=
  (-1) ^ s.val * (a - 1) ^ t.val * (a * z - 1) ^ u.val *
    ((2 * z + 1) * (a + 1)) ^ v.val

set_option maxHeartbeats 800000 in
-- Sixteen cases, each with a polynomial square-defect certificate.
set_option linter.unusedSimpArgs false in
/-- All fifteen nonidentity representatives have a dyadic square obstruction.
This calculation works in any Dedekind domain with a prime where `a` has order one. -/
theorem not_isSquare_kummerTwoSquareClassRepresentative
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) (a z : R)
    (ha : a ^ 3 = 2) (hz : z ^ 2 + z + 1 = 0)
    (haP : a ∈ P) (haP2 : a ∉ P ^ 2)
    (s t u v : Fin 2) (hn : s.val + t.val + u.val + v.val ≠ 0) :
    ¬ IsSquare (kummerTwoSquareClassRepresentative a z s t u v) := by
  have h2 : (2 : R) ∈ P ^ 3 := ha ▸ Ideal.pow_mem_pow haP 3
  have h22 : (2 : R) ∈ P ^ 2 := Ideal.pow_le_pow_right (by decide : 2 ≤ 3) h2
  have h2P : (2 : R) ∈ P := Ideal.pow_le_self (by decide : 3 ≠ 0) h2
  have haQ : Ideal.Quotient.mk P a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr haP
  have htwo : (2 : R ⧸ P) = 0 := by
    simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr h2P
  have hzQ : (Ideal.Quotient.mk P z) ^ 2 + Ideal.Quotient.mk P z + 1 = 0 := by
    simpa only [map_add, map_pow, map_one, map_zero] using congrArg (Ideal.Quotient.mk P) hz
  have hz0 : Ideal.Quotient.mk P z ≠ 0 := by
    intro h
    simp [h] at hzQ
  have hz1 : Ideal.Quotient.mk P z + 1 ≠ 0 := by
    intro h
    have hh : Ideal.Quotient.mk P z = -1 := eq_neg_of_add_eq_zero_left h
    simp [hh] at hzQ
  fin_cases s <;> fin_cases t <;> fin_cases u <;> fin_cases v
  all_goals dsimp only [kummerTwoSquareClassRepresentative]
  · exact (hn rfl).elim
  · -- Class 0001; square defect of order 1.
    apply not_isSquare_of_defect_one P a (1) (a ^ 2 * z + 2 * z + 1) _ haP haP2 h22
    · intro hc
      have hh := Ideal.Quotient.eq_zero_iff_mem.mpr hc
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
        haQ, htwo, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0)] at hh
      simp_all
    · linear_combination (-z) * ha
  · -- Class 0010; square defect of order 1.
    apply not_isSquare_of_defect_one P a (1) (-a ^ 2 + z) _ haP haP2 h22
    · intro hc
      have hh := Ideal.Quotient.eq_zero_iff_mem.mpr hc
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
        haQ, htwo, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0)] at hh
      simp_all
    · linear_combination (1) * ha
  · -- Class 0011; square defect of order 1.
    apply not_isSquare_of_defect_one P a (1)
      (-a ^ 2 * z - a ^ 2 + 2 * a * z ^ 2 + a * z + 2 * z ^ 2 - z - 1) _ haP haP2 h22
    · intro hc
      have hh := Ideal.Quotient.eq_zero_iff_mem.mpr hc
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
        haQ, htwo, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0)] at hh
      exact hz1 (by linear_combination -hh)
    · linear_combination (z + 1) * ha
  · -- Class 0100; square defect of order 1.
    apply not_isSquare_of_defect_one P a (1) (-a ^ 2 + 1) _ haP haP2 h22
    · intro hc
      have hh := Ideal.Quotient.eq_zero_iff_mem.mpr hc
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
        haQ, htwo, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0)] at hh
      simp_all
    · linear_combination (1) * ha
  · -- Class 0101; square defect of order 3.
    apply not_isSquare_of_defect_three P hP a (a + 1) (a ^ 2 * z - a - z - 1) _ haP haP2 h2
    · intro hc
      have hh := Ideal.Quotient.eq_zero_iff_mem.mpr hc
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
        haQ, htwo, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0)] at hh
      exact hz1 (by linear_combination -hh)
    · linear_combination (-a ^ 2 * z + a + z + 1) * ha
  · -- Class 0110; square defect of order 1.
    apply not_isSquare_of_defect_one P a (1) (a * z - z - 1) _ haP haP2 h22
    · intro hc
      have hh := Ideal.Quotient.eq_zero_iff_mem.mpr hc
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
        haQ, htwo, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0)] at hh
      exact hz1 (by linear_combination -hh)
    · linear_combination (0) * ha
  · -- Class 0111; square defect of order 1.
    apply not_isSquare_of_defect_one P a (1)
      (2 * a ^ 2 * z ^ 2 + 2 * a ^ 2 * z - 2 * a * z - a - 2 * z ^ 2 - z) _ haP haP2 h22
    · intro hc
      have hh := Ideal.Quotient.eq_zero_iff_mem.mpr hc
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
        haQ, htwo, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0)] at hh
      simp_all
    · linear_combination (-z) * ha
  · -- Class 1000; square defect of order 3.
    apply not_isSquare_of_defect_three P hP a (1) (-1) _ haP haP2 h2
    · intro hc
      have hh := Ideal.Quotient.eq_zero_iff_mem.mpr hc
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
        haQ, htwo, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0)] at hh
      simp_all
    · linear_combination (1) * ha
  · -- Class 1001; square defect of order 1.
    apply not_isSquare_of_defect_one P a (1) (-a ^ 2 * z - a ^ 2 - 2 * z - 1) _ haP haP2 h22
    · intro hc
      have hh := Ideal.Quotient.eq_zero_iff_mem.mpr hc
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
        haQ, htwo, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0)] at hh
      simp_all
    · linear_combination (z + 1) * ha
  · -- Class 1010; square defect of order 1.
    apply not_isSquare_of_defect_one P a (1) (-z) _ haP haP2 h22
    · intro hc
      have hh := Ideal.Quotient.eq_zero_iff_mem.mpr hc
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
        haQ, htwo, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0)] at hh
      simp_all
    · linear_combination (0) * ha
  · -- Class 1011; square defect of order 1.
    apply not_isSquare_of_defect_one P a (1)
      (a ^ 2 * z - 2 * a * z ^ 2 - a * z - 2 * z ^ 2 + z + 1) _ haP haP2 h22
    · intro hc
      have hh := Ideal.Quotient.eq_zero_iff_mem.mpr hc
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
        haQ, htwo, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0)] at hh
      simp_all
    · linear_combination (-z) * ha
  · -- Class 1100; square defect of order 1.
    apply not_isSquare_of_defect_one P a (1) (-1) _ haP haP2 h22
    · intro hc
      have hh := Ideal.Quotient.eq_zero_iff_mem.mpr hc
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
        haQ, htwo, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0)] at hh
      simp_all
    · linear_combination (0) * ha
  · -- Class 1101; square defect of order 3.
    apply not_isSquare_of_defect_three P hP a (a + 1) (-a ^ 2 * z - a ^ 2 - a + z) _ haP haP2 h2
    · intro hc
      have hh := Ideal.Quotient.eq_zero_iff_mem.mpr hc
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
        haQ, htwo, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0)] at hh
      simp_all
    · linear_combination (a ^ 2 * z + a ^ 2 + a - z) * ha
  · -- Class 1110; square defect of order 1.
    apply not_isSquare_of_defect_one P a (1) (-a ^ 2 - a * z + z + 1) _ haP haP2 h22
    · intro hc
      have hh := Ideal.Quotient.eq_zero_iff_mem.mpr hc
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
        haQ, htwo, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0)] at hh
      simp_all
    · linear_combination (1) * ha
  · -- Class 1111; square defect of order 1.
    apply not_isSquare_of_defect_one P a (1)
      (-2 * a ^ 2 * z ^ 2 - 2 * a ^ 2 * z - a ^ 2 + 2 * a * z + a + 2 * z ^ 2 + z) _ haP haP2 h22
    · intro hc
      have hh := Ideal.Quotient.eq_zero_iff_mem.mpr hc
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
        haQ, htwo, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0)] at hh
      simp_all
    · linear_combination (z + 1) * ha

/-- An unramified extension preserves the order-one property of the dyadic cube root. -/
theorem map_cubeRoot_notMem_sq_of_unramified
    (L : Type*) [Field L] [NumberField L] [Algebra K₀ L]
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(2 : ℤ)})]
    [Algebra.IsUnramifiedAt (𝓞 K₀) P]
    (a : 𝓞 K₀) (ha : a ^ 3 = 2) :
    algebraMap (𝓞 K₀) (𝓞 L) a ∈ P ∧ algebraMap (𝓞 K₀) (𝓞 L) a ∉ P ^ 2 := by
  classical
  let Q := P.under (𝓞 K₀)
  have : Q.LiesOver (Ideal.span {(2 : ℤ)}) :=
    Ideal.LiesOver.tower_bot P Q (Ideal.span {(2 : ℤ)})
  have hQ : Q = Ideal.span {a} := primeAboveTwo_eq_span_cubeRoot Q a ha
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have ham0 : algebraMap (𝓞 K₀) (𝓞 L) a ≠ 0 :=
    (map_eq_zero_iff _ (RingOfIntegers.algebraMap.injective K₀ L)).not.mpr ha0
  have hP : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (p := Ideal.span {(2 : ℤ)}) (by simp) P
  have hmap : Q.map (algebraMap (𝓞 K₀) (𝓞 L)) ≠ ⊥ := by
    rw [hQ, Ideal.map_span, Set.image_singleton]
    simpa using ham0
  have hc := Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count Q P hmap
  rw [Ideal.ramificationIdx_eq_one P (𝓞 K₀), hQ, Ideal.map_span,
    Set.image_singleton] at hc
  constructor
  · exact (Ideal.mem_of_liesOver P Q a).mp (by rw [hQ]; exact Ideal.subset_span (by simp))
  · rw [mem_prime_pow_iff_count P hP _ ham0 2, ← hc]
    decide

/-- Each of the fifteen nonidentity explicit classes ramifies at every prime above two
in any number field containing its square root. -/
theorem ramified_kummerTwoSquareClassRepresentative
    (a z : 𝓞 K₀) (ha : a ^ 3 = 2) (hz : z ^ 2 + z + 1 = 0)
    (s t u v : Fin 2) (hn : s.val + t.val + u.val + v.val ≠ 0)
    (L : Type*) [Field L] [NumberField L] [Algebra K₀ L] (y : L)
    (hy : y ^ 2 = algebraMap K₀ L
      ((kummerTwoSquareClassRepresentative a z s t u v : 𝓞 K₀) : K₀))
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(2 : ℤ)})] :
    ¬ Algebra.IsUnramifiedAt (𝓞 K₀) P := by
  intro hur
  let := hur
  have hP : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (p := Ideal.span {(2 : ℤ)}) (by simp) P
  obtain ⟨haP, haP2⟩ := map_cubeRoot_notMem_sq_of_unramified L P a ha
  have hyint : IsIntegral ℤ y := by
    apply IsIntegral.of_pow (n := 2) (by decide)
    rw [hy]
    exact isIntegral_algebraMap_iff.mpr (RingOfIntegers.isIntegral_coe _)
  apply not_isSquare_kummerTwoSquareClassRepresentative P hP
    (algebraMap (𝓞 K₀) (𝓞 L) a) (algebraMap (𝓞 K₀) (𝓞 L) z)
    (by simpa only [map_pow, map_ofNat] using congrArg (algebraMap (𝓞 K₀) (𝓞 L)) ha)
    (by simpa only [map_add, map_pow, map_one, map_zero] using
      congrArg (algebraMap (𝓞 K₀) (𝓞 L)) hz) haP haP2 s t u v hn
  let x : 𝓞 L := ⟨y, hyint⟩
  have hyO : x ^ 2 = algebraMap (𝓞 K₀) (𝓞 L)
      (kummerTwoSquareClassRepresentative a z s t u v) := by
    apply RingOfIntegers.ext
    exact hy
  refine ⟨x, ?_⟩
  rw [← pow_two, hyO]
  simp only [kummerTwoSquareClassRepresentative, map_mul, map_pow, map_neg,
    map_one, map_sub, map_add, map_ofNat]

/-- The inverse of the usual pure-cubic unit `1 + a + a²`. -/
def cubeRootTwoUnit {R : Type*} [CommRing R] (a : R) (ha : a ^ 3 = 2) : Rˣ where
  val := a - 1
  inv := a ^ 2 + a + 1
  val_inv := by linear_combination ha
  inv_val := by linear_combination ha

/-- A root of the third cyclotomic polynomial has cube one. -/
theorem cube_eq_one_of_thirdRoot {R : Type*} [CommRing R] (z : R)
    (hz : z ^ 2 + z + 1 = 0) : z ^ 3 = 1 := by
  linear_combination (z - 1) * hz

/-- Multiplying the cube root by a third root of unity gives its conjugate. -/
theorem conjugate_cubeRoot_two {R : Type*} [CommRing R] (a z : R)
    (ha : a ^ 3 = 2) (hz : z ^ 2 + z + 1 = 0) : (a * z) ^ 3 = 2 := by
  rw [mul_pow, ha, cube_eq_one_of_thirdRoot z hz, mul_one]

/-- The sign and two explicit cubic units generate all unit square classes.
Independence follows from the dyadic calculation, while Dirichlet's theorem bounds the index. -/
theorem kummerTwoUnit_square_representatives (a z : 𝓞 K₀)
    (ha : a ^ 3 = 2) (hz : z ^ 2 + z + 1 = 0) (w : (𝓞 K₀)ˣ) :
    ∃ (s t u : Fin 2) (v : (𝓞 K₀)ˣ),
      w = (-1) ^ s.val * cubeRootTwoUnit a ha ^ t.val *
        cubeRootTwoUnit (a * z) (conjugate_cubeRoot_two a z ha hz) ^ u.val * v ^ 2 := by
  classical
  let A := cubeRootTwoUnit a ha
  let B := cubeRootTwoUnit (a * z) (conjugate_cubeRoot_two a z ha hz)
  let S := (powMonoidHom (α := (𝓞 K₀)ˣ) 2).range
  let f := QuotientGroup.mk' S
  have : (Ideal.span {(2 : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 2
  obtain ⟨P, hPprime, hPover⟩ := (inferInstance :
    Nonempty ((Ideal.span {(2 : ℤ)}).primesOver (𝓞 K₀)))
  let := hPprime
  let := hPover
  have hP : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (p := Ideal.span {(2 : ℤ)}) (by simp) P
  have hPa : P = Ideal.span {a} := primeAboveTwo_eq_span_cubeRoot P a ha
  have haP : a ∈ P := by rw [hPa]; exact Ideal.subset_span (by simp)
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have haP2 : a ∉ P ^ 2 := by
    rw [mem_prime_pow_iff_count P hP a ha0 2, ← hPa,
      normalizedFactors_irreducible (Ideal.prime_of_isPrime hP inferInstance).irreducible,
      normalize_eq]
    simp
  have hinj : Function.Injective (binaryTripleProduct (f (-1)) (f A) (f B)) := by
    apply binaryTripleProduct_injective kummerTwoUnitSquareClasses_sq
    intro e he
    by_contra hne
    have hsum : e.1.val + e.2.1.val + e.2.2.val + (0 : Fin 2).val ≠ 0 := by
      intro h
      apply hne
      exact Prod.ext (Fin.ext (by dsimp; omega))
        (Prod.ext (Fin.ext (by dsimp; omega)) (Fin.ext (by dsimp; omega)))
    have hnonsq := not_isSquare_kummerTwoSquareClassRepresentative P hP a z ha hz
      haP haP2 e.1 e.2.1 e.2.2 0 hsum
    have he' : f ((-1) ^ e.1.val * A ^ e.2.1.val * B ^ e.2.2.val) = 1 := by
      simpa only [map_mul, map_pow, binaryTripleProduct] using he
    obtain ⟨v, hv⟩ := (QuotientGroup.eq_one_iff _).mp he'
    apply hnonsq
    refine ⟨(v : 𝓞 K₀), ?_⟩
    have hv' := congrArg Units.val hv
    simpa [kummerTwoSquareClassRepresentative, A, B, cubeRootTwoUnit, pow_two] using hv'.symm
  have hsurj := (hinj.bijective_of_nat_card_le (by
    simpa [Nat.card_prod, Nat.card_fin] using card_kummerTwoUnitSquareClasses_le)).2
  obtain ⟨e, he⟩ := hsurj (f w)
  have he' : f ((-1) ^ e.1.val * A ^ e.2.1.val * B ^ e.2.2.val) = f w := by
    simpa only [map_mul, map_pow, binaryTripleProduct] using he
  have hdiv : f (w / ((-1) ^ e.1.val * A ^ e.2.1.val * B ^ e.2.2.val)) = 1 := by
    rw [_root_.map_div, he', div_self']
  obtain ⟨v, hv⟩ := (QuotientGroup.eq_one_iff _).mp hdiv
  refine ⟨e.1, e.2.1, e.2.2, v, ?_⟩
  change v ^ 2 = w / ((-1) ^ e.1.val * A ^ e.2.1.val * B ^ e.2.2.val) at hv
  change w = (-1) ^ e.1.val * A ^ e.2.1.val * B ^ e.2.2.val * v ^ 2
  rw [hv, mul_comm, div_mul_cancel]

/-- A convenient generator above three, with an explicit dyadic square class. -/
theorem exists_kummerTwo_prime_generator (a z : 𝓞 K₀)
    (ha : a ^ 3 = 2) (hz : z ^ 2 + z + 1 = 0) :
    ∃ π : 𝓞 K₀, Ideal.span {π} = primeAboveThree K₀ ∧ π * (a + 1) = 2 * z + 1 := by
  have hb : (2 * z + 1) ^ 2 = -3 := by linear_combination 4 * hz
  have hQ2 := primeAboveThree_sq_eq_span a ha
  have hQ3 := primeAboveThree_cube_eq_span (2 * z + 1) hb
  have hdvd : a + 1 ∣ 2 * z + 1 := by
    apply Ideal.span_singleton_le_span_singleton.mp
    rw [← hQ2, ← hQ3]
    exact Ideal.pow_le_pow_right (by decide : 2 ≤ 3)
  obtain ⟨π, hπ⟩ := hdvd
  refine ⟨π, ?_, by simpa [mul_comm] using hπ.symm⟩
  have hQ0 : primeAboveThree K₀ ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (p := Ideal.span {(3 : ℤ)}) (by simp) _
  have hI := congrArg (fun x : 𝓞 K₀ ↦ Ideal.span {x}) hπ
  rw [← Ideal.span_singleton_mul_span_singleton, ← hQ2, ← hQ3, pow_succ] at hI
  exact (mul_left_cancel₀ (pow_ne_zero 2 hQ0) hI).symm

/-- Every global candidate is one of the explicit sixteen radicands times a nonzero square. -/
theorem kummerTwo_radicand_square_representative (a z : 𝓞 K₀)
    (ha : a ^ 3 = 2) (hz : z ^ 2 + z + 1 = 0)
    (π : 𝓞 K₀) (hπ : Ideal.span {π} = primeAboveThree K₀)
    (w : (𝓞 K₀)ˣ) (n : ℕ) (hn : n < 2) :
    ∃ (s t u v : Fin 2) (b : K₀), b ≠ 0 ∧
      ((w * π ^ n : 𝓞 K₀) : K₀) =
        ((kummerTwoSquareClassRepresentative a z s t u v : 𝓞 K₀) : K₀) * b ^ 2 := by
  obtain ⟨π₀, hπ₀, hπ₀eq⟩ := exists_kummerTwo_prime_generator a z ha hz
  obtain ⟨q, hq⟩ := Ideal.span_singleton_eq_span_singleton.mp (hπ₀.trans hπ.symm)
  obtain ⟨s, t, u, v, hv⟩ := kummerTwoUnit_square_representatives a z ha hz (w * q ^ n)
  have hvO := congrArg Units.val hv
  change (w : 𝓞 K₀) * (q : 𝓞 K₀) ^ n =
    (-1) ^ s.val * (a - 1) ^ t.val * (a * z - 1) ^ u.val * (v : 𝓞 K₀) ^ 2 at hvO
  have hfactor : (w : 𝓞 K₀) * π ^ n =
      (-1) ^ s.val * (a - 1) ^ t.val * (a * z - 1) ^ u.val * π₀ ^ n * (v : 𝓞 K₀) ^ 2 := by
    rw [← hq, mul_pow]
    calc
      (w : 𝓞 K₀) * (π₀ ^ n * (q : 𝓞 K₀) ^ n) =
          ((w : 𝓞 K₀) * (q : 𝓞 K₀) ^ n) * π₀ ^ n := by ring
      _ = _ := by rw [hvO]; ring
  have ha1 : a + 1 ≠ 0 := by
    intro h
    have hh : a = -1 := eq_neg_of_add_eq_zero_left h
    norm_num [hh] at ha
  have ha1K : (a : K₀) + 1 ≠ 0 := by
    simpa only [map_add, map_one] using (RingOfIntegers.coe_ne_zero_iff.mpr ha1)
  have hvK : (v : K₀) ≠ 0 := NumberField.Units.coe_ne_zero v
  refine ⟨s, t, u, ⟨n, hn⟩, (v : K₀) / ((a : K₀) + 1) ^ n,
    div_ne_zero hvK (pow_ne_zero n ha1K), ?_⟩
  rw [hfactor]
  have hπ₀K : (π₀ : K₀) * ((a : K₀) + 1) = 2 * (z : K₀) + 1 := by
    simpa only [map_mul, map_add, map_ofNat, map_one] using
      congrArg (algebraMap (𝓞 K₀) K₀) hπ₀eq
  simp only [kummerTwoSquareClassRepresentative, map_mul, map_pow, map_neg, map_one,
    map_sub, map_add, map_ofNat]
  rw [← hπ₀K]
  simp only [mul_pow]
  field_simp

/-- The dyadic square-class check: all unit-times-prime candidates unramified above two
are already squares in the sextic field. -/
theorem kummerTwoDyadicSquareClassCheck : KummerTwoDyadicSquareClassCheck := by
  intro π hπ w n hn L _ _ _ y hy _hgen hur
  obtain ⟨a, ha⟩ := exists_integral_cubeRoot_two
  obtain ⟨z, hz⟩ := exists_integral_thirdRoot
  obtain ⟨s, t, u, v, b, hb, hrepr⟩ :=
    kummerTwo_radicand_square_representative a z ha hz π hπ w n hn
  by_cases hzero : s.val + t.val + u.val + v.val = 0
  · have hs : s = 0 := Fin.ext (by change s.val = 0; omega)
    have ht : t = 0 := Fin.ext (by change t.val = 0; omega)
    have hu : u = 0 := Fin.ext (by change u.val = 0; omega)
    have hv : v = 0 := Fin.ext (by change v.val = 0; omega)
    refine ⟨b, ?_⟩
    simpa [hs, ht, hu, hv, kummerTwoSquareClassRepresentative, pow_two] using hrepr
  · have : (Ideal.span {(2 : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 2
    obtain ⟨P, hPprime, hPover⟩ := (inferInstance :
      Nonempty ((Ideal.span {(2 : ℤ)}).primesOver (𝓞 L)))
    let := hPprime
    let := hPover
    have hbL : algebraMap K₀ L b ≠ 0 := (map_ne_zero (algebraMap K₀ L)).mpr hb
    have hroot : (y / algebraMap K₀ L b) ^ 2 = algebraMap K₀ L
        ((kummerTwoSquareClassRepresentative a z s t u v : 𝓞 K₀) : K₀) := by
      rw [div_pow, hy, hrepr, map_mul, map_pow]
      field_simp
    exact (ramified_kummerTwoSquareClassRepresentative a z ha hz s t u v hzero
      L (y / algebraMap K₀ L b) hroot P (hur P)).elim

/-- Unramified outside three implies unramified at every prime above two. -/
theorem KummerTwoUnramifiedOutsideThree.at_two
    {L : Type*} [Field L] [NumberField L] [Algebra K₀ L]
    (hur : KummerTwoUnramifiedOutsideThree L)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(2 : ℤ)})] :
    Algebra.IsUnramifiedAt (𝓞 K₀) P := by
  let Q := P.under (𝓞 K₀)
  have hQover : Q.LiesOver (Ideal.span {(2 : ℤ)}) :=
    Ideal.LiesOver.tower_bot P Q (Ideal.span {(2 : ℤ)})
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (p := Ideal.span {(2 : ℤ)}) (by simp) Q
  have hQthree : Q ≠ primeAboveThree K₀ := by
    intro h
    have h2 := Ideal.over_def Q (Ideal.span {(2 : ℤ)})
    rw [h, ← Ideal.over_def (primeAboveThree K₀) (Ideal.span {(3 : ℤ)})] at h2
    have hm : (2 : ℤ) ∈ Ideal.span {(3 : ℤ)} := by
      rw [← h2]
      exact Ideal.subset_span (by simp)
    norm_num [Ideal.mem_span_singleton] at hm
  exact hur Q hQ hQthree P

/-- R7: there is no quadratic extension of the auxiliary sextic field unramified outside three. -/
theorem no_quadratic_extension_auxiliary
    (L : Type*) [Field L] [NumberField L] [Algebra K₀ L] [FiniteDimensional K₀ L]
    (hur : KummerTwoUnramifiedOutsideThree L) : Module.finrank K₀ L ≠ 2 := by
  intro hdegree
  obtain ⟨π, w, n, y, hπ, hn, hy, hgen⟩ := kummer_two_quadratic_reduction L hdegree hur
  obtain ⟨b, hb⟩ := kummerTwoDyadicSquareClassCheck π hπ w n hn L y hy hgen
    (fun P _ _ ↦ hur.at_two P)
  have hs : y ^ 2 = (algebraMap K₀ L b) ^ 2 := by
    rw [hy, hb, map_mul, pow_two]
  have hmem : y ∈ (⊥ : IntermediateField K₀ L) := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with h | h
    · rw [h]
      exact IntermediateField.algebraMap_mem _ b
    · rw [h]
      exact (⊥ : IntermediateField K₀ L).neg_mem (IntermediateField.algebraMap_mem _ b)
  have hbot : K₀⟮y⟯ = ⊥ := adjoin_simple_eq_bot_iff.mpr hmem
  have htop : (⊤ : IntermediateField K₀ L) = ⊥ := hgen.symm.trans hbot
  have hone : Module.finrank K₀ L = 1 := by
    rw [← IntermediateField.finrank_top', htop, IntermediateField.finrank_bot]
  omega

end ThreeAdicPlan
