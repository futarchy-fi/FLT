/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.RationalComplexConjugation
public import FLT.GroupScheme.SortedFiltrationCoefficientQuotient

/-!
# Purity of sorted finite-level character models

A scalar action of complex conjugation distinguishes the two parts of a sorted
extension. Trivial conjugation kills the multiplicative part; negative
conjugation kills the constant quotient. This works at every three-power level.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

local notation "Γ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

/-- A point killed by two and by a power of three is zero. -/
theorem eq_zero_of_two_and_three_power_nsmul
    {A : Type*} [AddCommGroup A] (n : ℕ) (a : A)
    (h2 : (2 : ℕ) • a = 0) (h3 : (3 ^ n) • a = 0) : a = 0 := by
  have hcoprime : Nat.Coprime 2 (3 ^ n) := (by decide : Nat.Coprime 2 3).pow_right n
  have horder : addOrderOf a ∣ 1 := by
    rw [← hcoprime.gcd_eq_one]
    exact Nat.dvd_gcd (addOrderOf_dvd_iff_nsmul_eq_zero.mpr h2)
      (addOrderOf_dvd_iff_nsmul_eq_zero.mpr h3)
  exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one horder)

/-- Additive maps between bounded three-primary modules respect three-adic scalars. -/
theorem map_padic_smul_of_pow_kills
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module ℤ_[3] A] [Module ℤ_[3] B]
    (n : ℕ) (hA : ∀ a : A, (3 ^ n) • a = 0) (hB : ∀ b : B, (3 ^ n) • b = 0)
    (f : A →+ B) (r : ℤ_[3]) (a : A) : f (r • a) = r • f a := by
  rw [padic_smul_eq_nsmul_of_pow_kills 3 n hA,
    padic_smul_eq_nsmul_of_pow_kills 3 n hB, map_nsmul]

/-- A multiplicative filtration has cyclotomic action at every bounded three-power level. -/
theorem HasFiltration.pure_cyclotomic_of_pow_kills
    {A : FiniteFlatObject ZInvTwo} [Module ℤ_[3] A.points]
    (hA : HasFiltration A muThree) (n : ℕ)
    (hkill : ∀ a : A.points, (3 ^ n) • a = 0) :
    Pure A.points (fun σ : Γ ↦
      (cyclotomicCharacter (AlgebraicClosure ℚ) 3 σ.toRingEquiv).val) := by
  intro σ a
  rw [padic_smul_eq_nsmul_of_pow_kills 3 n hkill]
  exact A.points.cyclotomic_nsmul_of_characterDual_trivial 3 n hkill
    (pure_one_characterDual_of_muThree_filtration A hA) σ a

/-- Scalar complex conjugation forces a sorted three-primary model to have pure action. -/
theorem SortedFiniteFlatExtension.pure_of_scalar_conjugation
    {H : FiniteFlatObject ZInvTwo} [Module ℤ_[3] H.points]
    (S : SortedFiniteFlatExtension H) (n : ℕ)
    (hkill : ∀ x : H.points, (3 ^ n) • x = 0)
    (hc : (∀ x : H.points, rationalComplexConjugation • x = x) ∨
      (∀ x : H.points, rationalComplexConjugation • x = -x)) :
    Pure H.points (1 : Γ → ℤ) ∨
      Pure H.points (fun σ : Γ ↦
        (cyclotomicCharacter (AlgebraicClosure ℚ) 3 σ.toRingEquiv).val) := by
  let i := FiniteFlatObject.pointMap S.extension.inclusion
  let q := FiniteFlatObject.pointMap S.extension.quotient
  have hleftKill (a : S.left.points) : (3 ^ n) • a = 0 := by
    apply S.extension.pointsInjective
    rw [map_nsmul, hkill, map_zero]
  have hrightKill (b : S.right.points) : (3 ^ n) • b = 0 := by
    obtain ⟨x, rfl⟩ := S.extension.pointsSurjective b
    rw [← map_nsmul, hkill, map_zero]
  let instLeftModule : Module ℤ_[3] S.left.points := primePowerModule 3 n hleftKill
  have hleft := S.leftFiltration.pure_cyclotomic_of_pow_kills n hleftKill
  have hleftConj (a : S.left.points) : rationalComplexConjugation • a = -a := by
    simpa only [rationalComplexConjugation_cyclotomic, neg_smul, one_smul] using
      hleft rationalComplexConjugation a
  have hright (σ : Γ) (b : S.right.points) : σ • b = b := by
    simpa using pure_one_of_constantThree_filtration S.right S.rightFiltration σ b
  rcases hc with hplus | hminus
  · left
    have hzero (a : S.left.points) : a = 0 := by
      have heq : -a = a := S.extension.pointsInjective (show i (-a) = i a from calc
        i (-a) = i (rationalComplexConjugation • a) := congrArg i (hleftConj a).symm
        _ = rationalComplexConjugation • i a := map_smul i _ a
        _ = i a := hplus (i a))
      exact eq_zero_of_two_and_three_power_nsmul n a
        (by simpa only [two_nsmul] using eq_neg_iff_add_eq_zero.mp heq.symm) (hleftKill a)
    intro σ x
    have hd : σ • x - x = 0 := by
      obtain ⟨a, ha⟩ := S.galoisDifference_mem σ x
      rw [← ha, hzero a, map_zero]
    simpa using sub_eq_zero.mp hd
  · right
    have hzero (b : S.right.points) : b = 0 := by
      obtain ⟨x, rfl⟩ := S.extension.pointsSurjective b
      have heq : -(q x) = q x := calc
        -(q x) = q (-x) := (map_neg q x).symm
        _ = q (rationalComplexConjugation • x) := congrArg q (hminus x).symm
        _ = rationalComplexConjugation • q x := map_smul q _ x
        _ = q x := hright _ _
      exact eq_zero_of_two_and_three_power_nsmul n (q x)
        (by simpa only [two_nsmul] using eq_neg_iff_add_eq_zero.mp heq.symm) (hrightKill (q x))
    intro σ x
    obtain ⟨a, ha⟩ := (S.extension.pointsExact x).mp (hzero (q x))
    rw [← ha, ← map_smul, hleft σ a]
    exact map_padic_smul_of_pow_kills n hleftKill hkill i.toAddMonoidHom _ a

end ThreeAdicPlan
