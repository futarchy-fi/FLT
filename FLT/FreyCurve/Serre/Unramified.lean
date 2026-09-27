/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.GoodReduction
public import FLT.FreyCurve.Serre.LocalInertia
public import FLT.FreyCurve.Serre.LocalTorsion
public import FLT.FreyCurve.Serre.Semistable
public import FLT.FreyCurve.Serre.TateUnramified

/-!
# Frey torsion is unramified outside 2p

At multiplicative primes different from 2, the Frey discriminant has valuation
an exact p-th power: its denominator is a unit and its numerator is a 2p-th
power. The tame Kummer criterion therefore kills all inertia on p-torsion.
-/

@[expose] public section

open NumberField WeierstrassCurve ValuativeRel
open scoped WeierstrassCurve.Affine

namespace FreyCurve

/-- At multiplicative reduction away from 2, the inverse j-valuation is a p-th
power in the base value group. -/
theorem inv_valuation_j_eq_pow (P : FreyPackage) {K : Type*}
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Algebra ℚ K]
    [(P.freyCurve.baseChange K).HasMultiplicativeReduction 𝒪[K]]
    (h2 : valuation K (2 : K) = 1) :
    (valuation K (P.freyCurve.baseChange K).j)⁻¹ =
      valuation K (algebraMap ℚ K (((P.a : ℚ) * P.b * P.c) ^ 2)) ^ P.p := by
  rw [WeierstrassCurve.valuation_j_eq, inv_inv]
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, FreyCurve.Δ,
    map_div₀, map_pow, map_ofNat, h2, one_pow, div_one, pow_mul]

set_option backward.isDefEq.respectTransparency false in
/-- Inertia acts trivially on the entire p-torsion of the Frey curve at every
prime different from 2 and p. -/
theorem torsion_isUnramifiedAt (P : FreyPackage) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hℓp : ℓ ≠ P.p) :
    (P.freyCurve.galoisRep P.p P.hppos).IsUnramifiedAt
      hℓ.toHeightOneSpectrumRingOfIntegersRat := by
  classical
  have hn := prime_isUnit_adicCompletionIntegers P.pp hℓ hℓp
  let v := hℓ.toHeightOneSpectrumRingOfIntegersRat
  let K := v.adicCompletion ℚ
  let Ω := AlgebraicClosure K
  let : ValuativeRel K := completionValuativeRel v
  let : IsNonarchimedeanLocalField K := completion_isNonarchimedeanLocalField v
  let A := localClosureValuation v
  have hA : (A.comap (algebraMap K Ω)).toSubring = (algebraMap 𝒪[K] K).range := by
    rw [localClosureValuation_comap]
    have h : algebraMap (v.adicCompletionIntegers ℚ) K =
        (v.adicCompletionIntegers ℚ).subtype := by
      ext x
      rfl
    rw [h]
    change (v.adicCompletionIntegers ℚ).toSubring.subtype.range = _
    rw [Subring.range_subtype, Subring.algebraMap_def, Subring.range_subtype]
    exact (completion_integerRing_eq v).symm
  let f : v.adicCompletionIntegers ℚ →+* A :=
    algebraMap (v.adicCompletionIntegers ℚ) (IntegralClosure (v.adicCompletionIntegers ℚ) Ω)
  have hnA : IsUnit (P.p : A) := by simpa only [map_natCast] using hn.map f
  have h2A : IsUnit ((2 : ℕ) : A) := by
    simpa only [map_natCast] using
      (prime_isUnit_adicCompletionIntegers Nat.prime_two hℓ hℓ2).map f
  have h2 : valuation K (2 : K) = 1 := by
    have h := (A.valuation_eq_one_iff ((2 : ℕ) : A)).mp h2A
    change A.valuation (A.subtype ((2 : ℕ) : A)) = 1 at h
    rw [map_natCast] at h
    apply (A.isEquiv_comap_of_integerRing hA).eq_one_iff_eq_one.mp
    change A.valuation (algebraMap K Ω ((2 : ℕ) : K)) = 1
    rw [map_natCast]
    exact h
  constructor
  intro σ hσ
  change (P.freyCurve.galoisRep P.p P.hppos).toLocal v σ = 1
  have heq : (P.freyCurve.galoisRep P.p P.hppos).toLocal v =
      (P.freyCurve.galoisRep P.p P.hppos).map (algebraMap ℚ K) := by
    unfold GaloisRep.toLocal
    congr 1
    exact Subsingleton.elim _ _
  rw [heq]
  apply P.freyCurve.galoisRep_map_eq_one P.p P.hppos σ
  intro Q hQ
  let σA := localClosureDecomposition v σ
  have hσA := localClosureDecomposition_mem_inertia v σ hσ
  have hmap (X : (P.freyCurve⁄Ω).Point) :
      Affine.Point.map (W' := P.freyCurve.baseChange K)
        (σA : Ω ≃ₐ[K] Ω).toAlgHom X =
        Affine.Point.map (σ.toAlgHom.restrictScalars ℚ) X := by
    cases X <;> rfl
  obtain hgood | hmult := P.good_or_multiplicative 𝒪[K] K
  · let := hgood
    have hfix := inertia_fixes_torsion_of_good_reduction 𝒪[K] K Ω
      (P.freyCurve.baseChange K) A hA hnA σA hσA Q hQ
    rw [hmap] at hfix
    exact hfix
  · let := hmult
    have habc : ((P.a : ℚ) * P.b * P.c) ^ 2 ≠ 0 := by
      exact_mod_cast pow_ne_zero 2 (mul_ne_zero (mul_ne_zero P.ha0 P.hb0) P.hc0)
    let b : Kˣ := Units.mk0 (algebraMap ℚ K (((P.a : ℚ) * P.b * P.c) ^ 2))
      ((map_ne_zero (algebraMap ℚ K)).mpr habc)
    simpa only [hmap] using
      (P.freyCurve.baseChange K).inertia_fixes_torsion_of_multiplicative
        A hA hnA b (inv_valuation_j_eq_pow P h2) σA hσA Q hQ

end FreyCurve
