/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.AbsoluteGaloisGroup.FundamentalTame
public import Mathlib.RingTheory.Filtration
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Higher ramification congruences

The lower filtration is defined by congruences on every integer. It is normal,
decreasing, and eventually trivial for a finite faithful action on a DVR.
-/

@[expose] public section

open IsLocalRing
open scoped Pointwise

namespace LocalRamification

section LocalRing

variable (R G : Type*) [CommRing R] [IsLocalRing R] [Group G] [MulSemiringAction G R]

/-- The lower ramification group at a nonnegative integer index. -/
def ramificationGroup (i : ℕ) : Subgroup G :=
  (maximalIdeal R ^ (i + 1)).inertia G

/-- Membership is the congruence on every integer. -/
theorem mem_ramificationGroup_iff (i : ℕ) (σ : G) :
    σ ∈ ramificationGroup R G i ↔ ∀ x : R, σ • x - x ∈ maximalIdeal R ^ (i + 1) :=
  Iff.rfl

/-- Index one agrees with the first group used to define wild inertia. -/
@[simp] theorem ramificationGroup_one : ramificationGroup R G 1 = firstGroup R G := rfl

/-- The lower groups form a decreasing filtration. -/
theorem ramificationGroup_antitone : Antitone (ramificationGroup R G) := by
  intro i j hij σ hσ x
  exact Ideal.pow_le_pow_right (by omega : i + 1 ≤ j + 1) (hσ x)

/-- Every lower ramification group is normal in the acting group. -/
instance ramificationGroup_normal (i : ℕ) : (ramificationGroup R G i).Normal := by
  rw [Subgroup.normal_iff_map_conj_eq]
  intro g
  have hm : g • maximalIdeal R = maximalIdeal R :=
    IsLocalRing.map_ringEquiv_maximalIdeal (MulSemiringAction.toRingAut G R g)
  have hp : g • (maximalIdeal R ^ (i + 1)) = maximalIdeal R ^ (i + 1) := by
    rw [smul_pow', hm]
  exact (Ideal.inertia_smul g _).symm.trans (congrArg (Ideal.inertia G) hp)

end LocalRing

variable (R G : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Group G] [MulSemiringAction G R]

/-- First ramification acts trivially on every successive ideal quotient. -/
theorem firstGroup_sub_mem_pow_succ {σ : G} (hσ : σ ∈ firstGroup R G)
    {n : ℕ} {x : R} (hx : x ∈ maximalIdeal R ^ n) :
    σ • x - x ∈ maximalIdeal R ^ (n + 1) := by
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨z, hz, hzr⟩ := firstGroup_ratio hσ hx0
  have hz1 : z - 1 ∈ maximalIdeal R := by
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    change residue R (z - 1) = 0
    rw [map_sub, hzr, map_one, sub_self]
  rw [hz, ← sub_one_mul, pow_succ']
  exact Ideal.mul_mem_mul hz1 hx

/-- A faithful action is separated by the lower ramification groups. -/
theorem iInf_ramificationGroup [FaithfulSMul G R] :
    ⨅ i, ramificationGroup R G i = ⊥ := by
  apply le_antisymm _ bot_le
  intro σ hσ
  apply Subgroup.mem_bot.mpr
  apply eq_of_smul_eq_smul (α := R)
  intro x
  have hx : σ • x - x ∈ ⨅ n : ℕ, maximalIdeal R ^ n := by
    rw [Ideal.mem_iInf]
    intro n
    exact Ideal.pow_le_pow_right (Nat.le_succ n) ((Subgroup.mem_iInf.mp hσ n) x)
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top,
    Ideal.mem_bot] at hx
  simpa using sub_eq_zero.mp hx

/-- For a finite faithful action, some lower ramification group is trivial. -/
theorem exists_ramificationGroup_eq_bot [FaithfulSMul G R] [Finite G] :
    ∃ i, ramificationGroup R G i = ⊥ := by
  classical
  let := Fintype.ofFinite G
  have hex : ∀ σ : G, ∃ i, σ ∈ ramificationGroup R G i → σ = 1 := by
    intro σ
    by_cases hσ : σ = 1
    · exact ⟨0, fun _ ↦ hσ⟩
    by_contra! h
    have hmem : σ ∈ ⨅ i, ramificationGroup R G i := Subgroup.mem_iInf.mpr (fun i ↦ (h i).1)
    rw [iInf_ramificationGroup R G] at hmem
    exact hσ (Subgroup.mem_bot.mp hmem)
  choose n hn using hex
  refine ⟨Finset.univ.sup n, le_antisymm ?_ bot_le⟩
  intro σ hσ
  apply Subgroup.mem_bot.mpr
  exact hn σ (ramificationGroup_antitone R G (Finset.le_sup (Finset.mem_univ σ)) hσ)

/-- Successive differences, recorded on every integer, form an additive character.
This construction does not require choosing residue representatives. -/
noncomputable def ramificationDifference (i : ℕ) (hi : 1 ≤ i) :
    ramificationGroup R G i →* Multiplicative (R → R ⧸ maximalIdeal R ^ (i + 2)) where
  toFun σ := Multiplicative.ofAdd fun x ↦ Ideal.Quotient.mk _ (σ.1 • x - x)
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    funext x
    simp
  map_mul' σ τ := by
    apply congrArg Multiplicative.ofAdd
    funext x
    change Ideal.Quotient.mk _ ((σ.1 * τ.1) • x - x) =
      Ideal.Quotient.mk _ (σ.1 • x - x) + Ideal.Quotient.mk _ (τ.1 • x - x)
    rw [← map_add, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    have hσ : σ.1 ∈ firstGroup R G := ramificationGroup_antitone R G hi σ.2
    have h := firstGroup_sub_mem_pow_succ R G hσ (τ.2 x)
    convert h using 1
    simp [mul_smul, smul_sub]
    ring

/-- The kernel of the difference character is exactly the next lower group. -/
theorem mem_ramificationDifference_ker (i : ℕ) (hi : 1 ≤ i)
    (σ : ramificationGroup R G i) :
    σ ∈ (ramificationDifference R G i hi).ker ↔
      σ.1 ∈ ramificationGroup R G (i + 1) := by
  change Multiplicative.ofAdd (fun x ↦ Ideal.Quotient.mk _ (σ.1 • x - x)) = 1 ↔ _
  change (fun x ↦ Ideal.Quotient.mk _ (σ.1 • x - x)) = (0 : R → R ⧸ maximalIdeal R ^ (i + 2)) ↔ _
  rw [funext_iff]
  simp only [Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem]
  rfl

/-- Divide the uniformizer difference by its known power divisor. -/
noncomputable def ramificationCoefficient {π : R} (hπ : Irreducible π)
    (i : ℕ) (σ : ramificationGroup R G i) : R :=
  Classical.choose (show π ^ (i + 1) ∣ σ.1 • π - π by
    have h : σ.1 • π - π ∈ maximalIdeal R ^ (i + 1) := σ.2 π
    rwa [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h)

/-- The coefficient is the actual normalized uniformizer difference. -/
theorem ramificationCoefficient_spec {π : R} (hπ : Irreducible π)
    (i : ℕ) (σ : ramificationGroup R G i) :
    σ.1 • π - π = π ^ (i + 1) * ramificationCoefficient R G hπ i σ :=
  Classical.choose_spec (show π ^ (i + 1) ∣ σ.1 • π - π by
    have h : σ.1 • π - π ∈ maximalIdeal R ^ (i + 1) := σ.2 π
    rwa [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h)

/-- Cancellation identifies the next congruence with vanishing of the residue coefficient. -/
theorem residue_coefficient_eq_zero_iff {π : R} (hπ : Irreducible π)
    (i : ℕ) (σ : ramificationGroup R G i) :
    residue R (ramificationCoefficient R G hπ i σ) = 0 ↔
      σ.1 • π - π ∈ maximalIdeal R ^ (i + 2) := by
  rw [residue_eq_zero_iff, hπ.maximalIdeal_eq,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton, Ideal.mem_span_singleton,
    ramificationCoefficient_spec R G hπ]
  rw [show i + 2 = (i + 1) + 1 from rfl, pow_succ]
  exact (mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero)).symm

/-- The normalized uniformizer difference is an additive residue character. -/
noncomputable def ramificationResidueCharacter {π : R} (hπ : Irreducible π)
    (i : ℕ) (hi : 1 ≤ i) : ramificationGroup R G i →* Multiplicative (ResidueField R) where
  toFun σ := Multiplicative.ofAdd (residue R (ramificationCoefficient R G hπ i σ))
  map_one' := by
    change residue R (ramificationCoefficient R G hπ i 1) = 0
    rw [residue_coefficient_eq_zero_iff R G hπ]
    simp
  map_mul' σ τ := by
    change residue R (ramificationCoefficient R G hπ i (σ * τ)) =
      residue R (ramificationCoefficient R G hπ i σ) +
      residue R (ramificationCoefficient R G hπ i τ)
    rw [← map_add, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
      hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
    apply (mul_dvd_mul_iff_left (pow_ne_zero (i + 1) hπ.ne_zero)).mp
    have hσ : σ.1 ∈ firstGroup R G := ramificationGroup_antitone R G hi σ.2
    have h := firstGroup_sub_mem_pow_succ R G hσ (τ.2 π)
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    rw [← pow_succ]
    convert h using 1
    rw [mul_sub, mul_add, ← ramificationCoefficient_spec, ← ramificationCoefficient_spec,
      ← ramificationCoefficient_spec]
    simp [mul_smul, smul_sub]
    ring

/-- The next lower group is killed by the uniformizer residue character. -/
theorem ramificationResidueCharacter_kills_next {π : R} (hπ : Irreducible π)
    (i : ℕ) (hi : 1 ≤ i) (σ : ramificationGroup R G i)
    (hσ : σ.1 ∈ ramificationGroup R G (i + 1)) :
    ramificationResidueCharacter R G hπ i hi σ = 1 :=
  (residue_coefficient_eq_zero_iff R G hπ i σ).mpr (hσ π)

/-- Over a finite residue field the uniformizer congruence detects the next group. -/
theorem mem_next_iff_uniformizer [Finite (ResidueField R)] {π : R} (hπ : Irreducible π)
    (i : ℕ) (hi : 1 ≤ i) (σ : ramificationGroup R G i) :
    σ.1 ∈ ramificationGroup R G (i + 1) ↔
      σ.1 • π - π ∈ maximalIdeal R ^ (i + 2) := by
  refine ⟨fun h ↦ h π, fun hπσ x ↦ ?_⟩
  change σ.1 • x - x ∈ maximalIdeal R ^ (i + 2)
  classical
  let := Fintype.ofFinite (ResidueField R)
  let q := Fintype.card (ResidueField R)
  have hm : ∀ y ∈ maximalIdeal R, σ.1 • y - y ∈ maximalIdeal R ^ (i + 2) := by
    intro y hy
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hy
    obtain ⟨z, rfl⟩ := hy
    have h₁ := (maximalIdeal R ^ (i + 2)).mul_mem_right (σ.1 • z) hπσ
    have h₂ := Ideal.mul_mem_mul
      (show π ∈ maximalIdeal R from hπ.not_isUnit) (σ.2 z)
    have h₂' : π * (σ.1 • z - z) ∈ maximalIdeal R ^ (i + 2) := by
      simpa [pow_succ'] using h₂
    convert (maximalIdeal R ^ (i + 2)).add_mem h₁ h₂' using 1
    rw [smul_mul']
    ring
  have hxq : x ^ q - x ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, map_sub, map_pow, FiniteField.pow_card, sub_self]
  have hdiff := hm _ hxq
  have hres : residue R (σ.1 • x) = residue R x := by
    apply sub_eq_zero.mp
    rw [← map_sub, residue_eq_zero_iff]
    exact firstGroup_le_inertia R G (ramificationGroup_antitone R G hi σ.2) x
  have hsum : (∑ j ∈ Finset.range q, (σ.1 • x) ^ j * x ^ (q - 1 - j)) ∈
      maximalIdeal R := by
    rw [← residue_eq_zero_iff]
    simp only [map_sum, map_mul, map_pow, hres]
    rw [geom_sum₂_self, FiniteField.cast_card_eq_zero, zero_mul]
  have hpow : σ.1 • (x ^ q) - x ^ q ∈ maximalIdeal R ^ (i + 2) := by
    rw [smul_pow', ← geom_sum₂_mul]
    simpa [pow_succ'] using Ideal.mul_mem_mul hsum (σ.2 x)
  convert (maximalIdeal R ^ (i + 2)).sub_mem hpow hdiff using 1
  rw [smul_sub]
  ring

/-- The explicit residue character has exactly the next lower group as kernel. -/
theorem ramificationResidueCharacter_ker [Finite (ResidueField R)] {π : R}
    (hπ : Irreducible π) (i : ℕ) (hi : 1 ≤ i) :
    (ramificationResidueCharacter R G hπ i hi).ker =
      (ramificationGroup R G (i + 1)).comap (ramificationGroup R G i).subtype := by
  ext σ
  exact (residue_coefficient_eq_zero_iff R G hπ i σ).trans
    (mem_next_iff_uniformizer R G hπ i hi σ).symm

/-- Embed a successive lower quotient into the additive residue field using the
chosen uniformizer. The kernel is identified with the next group above. -/
noncomputable def ramificationQuotientEmbedding [Finite (ResidueField R)] {π : R}
    (hπ : Irreducible π) (i : ℕ) (hi : 1 ≤ i) :
    ramificationGroup R G i ⧸
      (ramificationGroup R G (i + 1)).comap (ramificationGroup R G i).subtype →*
        Multiplicative (ResidueField R) :=
  QuotientGroup.lift _ (ramificationResidueCharacter R G hπ i hi)
    (by rw [ramificationResidueCharacter_ker])

/-- The residue-field map on the successive quotient is injective. -/
theorem ramificationQuotientEmbedding_injective [Finite (ResidueField R)] {π : R}
    (hπ : Irreducible π) (i : ℕ) (hi : 1 ≤ i) :
    Function.Injective (ramificationQuotientEmbedding R G hπ i hi) := by
  intro a b
  refine Quotient.inductionOn₂' a b fun a b h ↦ ?_
  change ramificationResidueCharacter R G hπ i hi a =
    ramificationResidueCharacter R G hπ i hi b at h
  apply Quotient.sound'
  rw [QuotientGroup.leftRel_apply, ← ramificationResidueCharacter_ker R G hπ i hi]
  change ramificationResidueCharacter R G hπ i hi (a⁻¹ * b) = 1
  rw [map_mul, map_inv, h, inv_mul_cancel]

end LocalRamification
