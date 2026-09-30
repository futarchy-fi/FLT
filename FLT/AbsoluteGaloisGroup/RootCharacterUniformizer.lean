/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.AbsoluteGaloisGroup.RootCharacterIndependence

/-!
# Uniformizer independence and compatibility of root characters

Roots of any two uniformizers in the same positive degree have an integral
unit ratio. Their reduced inertia characters therefore agree. Compatibility
between degrees also holds without making compatible choices of roots.
-/

@[expose] public section

open NumberField

namespace LocalRoot

variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation3 "L" => AlgebraicClosure (v.adicCompletion K)
local notation3 "O" => v.adicCompletionIntegers K
local notation3 "A" => IntegralClosure O L

variable {n : ℕ} (hn : 0 < n)

include hn in
/-- Roots of uniformizers have an integral unit ratio in every positive degree. -/
theorem exists_unit_ratio_of_uniformizers {π π' : O}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    (hπ' : Valued.v π'.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α β : AlgebraicClosure (v.adicCompletion K)}
    (hα : α ^ n = algebraMap (v.adicCompletion K) L π.1)
    (hβ : β ^ n = algebraMap (v.adicCompletion K) L π'.1) :
    ∃ z : Aˣ, (z : A).1 = β / α := by
  have hne : π ≠ 0 :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero hπ
  have hassoc : Associated π π' := Ideal.span_singleton_eq_span_singleton.mp <|
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer
      K v hπ).symm.trans
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer
      K v hπ')
  obtain ⟨u, hu⟩ := hassoc
  have huval : π.1 * (u : O).1 = π'.1 := congrArg Subtype.val hu
  have hzpow : (β / α) ^ n = algebraMap O L (u : O) := by
    rw [div_pow, hβ, hα, ← huval, map_mul]
    rw [mul_div_cancel_left₀]
    · exact (IsScalarTower.algebraMap_apply O (v.adicCompletion K) L (u : O)).symm
    · exact (map_ne_zero (algebraMap (v.adicCompletion K) L)).mpr fun h ↦
        hne (Subtype.ext h)
  let z : A := ⟨β / α, IsIntegral.of_pow hn <| by
    rw [hzpow]
    exact isIntegral_algebraMap⟩
  have hzpowA : z ^ n = algebraMap O A (u : O) := by
    apply Subtype.ext
    exact hzpow.trans (IsScalarTower.algebraMap_apply O A L (u : O))
  have hzunit : IsUnit z := (isUnit_pow_iff hn.ne').mp <| by
    rw [hzpowA]
    exact IsUnit.map (algebraMap O A) u.isUnit
  exact ⟨hzunit.unit, congrArg Subtype.val hzunit.unit_spec⟩

/-- The character is independent of both the uniformizer and its chosen root. -/
theorem character_uniformizer_independent {π π' : O}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    (hπ' : Valued.v π'.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α β : AlgebraicClosure (v.adicCompletion K)}
    (hα : α ^ n = algebraMap (v.adicCompletion K) L π.1)
    (hβ : β ^ n = algebraMap (v.adicCompletion K) L π'.1) :
    character v hn
      (fun h ↦ IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero
        hπ' (Subtype.ext h)) hβ =
    character v hn
      (fun h ↦ IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero
        hπ (Subtype.ext h)) hα := by
  obtain ⟨z, hz⟩ := exists_unit_ratio_of_uniformizers v hn hπ hπ' hα hβ
  exact character_eq_of_unit_ratio v hn _ _ hα hβ z hz

/-- Characters in divisible degrees are compatible for arbitrary choices of roots. -/
theorem character_degree_mul_independent {a : v.adicCompletion K} (ha : a ≠ 0)
    {α : AlgebraicClosure (v.adicCompletion K)}
    (hα : α ^ n = algebraMap (v.adicCompletion K) L a)
    (m : ℕ) (hm : 0 < m) {β : AlgebraicClosure (v.adicCompletion K)}
    (hβ : β ^ (n * m) = algebraMap (v.adicCompletion K) L a)
    (σ : localInertiaGroup v) :
    character v (Nat.mul_pos hn hm) ha hβ σ ^ m = character v hn ha hα σ := by
  rw [character_degree_mul v hn ha m hm hβ σ]
  exact congrArg (fun c : localInertiaGroup v →* (IsLocalRing.ResidueField A)ˣ ↦ c σ)
    (character_root_independent v hn ha hα _)

end LocalRoot
