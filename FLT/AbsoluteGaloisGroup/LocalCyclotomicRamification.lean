/-
Copyright (c) 2026 Kelvin Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelvin Santos
-/
module

public import FLT.Mathlib.RingTheory.DiscreteValuationRing.EisensteinExtension
public import FLT.Mathlib.RingTheory.DiscreteValuationRing.TotalRamification
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-!
# The local prime cyclotomic polynomial

The shifted prime cyclotomic polynomial is Eisenstein over the p-adic integers.
This supplies the degree and integral ramification calculation for the local
cyclotomic extension.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

namespace LocalCyclotomic

variable (p : ℕ) [hp : Fact p.Prime]

/-- The polynomial of a primitive p-th root of unity minus one. -/
def shifted : ℤ_[p][X] := (cyclotomic p ℤ_[p]).comp (X + 1)

lemma shifted_monic : (shifted p).Monic := by
  simpa [shifted] using (cyclotomic.monic p ℤ_[p]).comp (monic_X_add_C 1) (by simp)

lemma shifted_natDegree : (shifted p).natDegree = p - 1 := by
  simp [shifted, natDegree_comp, natDegree_cyclotomic, Nat.totient_prime hp.out]

lemma shifted_coeff_zero : (shifted p).coeff 0 = p := by
  simp [shifted, coeff_zero_eq_eval_zero, eval_comp, eval_one_cyclotomic_prime]

/-- Eisenstein's criterion survives passage from integers to p-adic integers. -/
theorem shifted_isEisensteinAt : (shifted p).IsEisensteinAt (maximalIdeal ℤ_[p]) := by
  apply (shifted_monic p).isEisensteinAt_of_mem_of_notMem (maximalIdeal.isMaximal _).ne_top
  · intro i hi
    have hw := (cyclotomic_comp_X_add_one_isEisensteinAt p).isWeaklyEisensteinAt.map
      (Int.castRingHom ℤ_[p])
    have hmap : ((cyclotomic p ℤ).comp (X + 1)).map (Int.castRingHom ℤ_[p]) =
        shifted p := by simp [shifted, Polynomial.map_comp, map_cyclotomic]
    rw [hmap] at hw
    have := hw.mem hi
    simpa [Ideal.map_span, Set.image_singleton, PadicInt.maximalIdeal_eq_span_p] using this
  · rw [shifted_coeff_zero, PadicInt.maximalIdeal_eq_span_p,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact (irreducible_iff_prime.mp PadicInt.irreducible_p).not_dvd_one ∘
      (fun h ↦ (mul_dvd_mul_iff_left (show (p : ℤ_[p]) ≠ 0 from
        PadicInt.irreducible_p.ne_zero)).mp (by simpa [pow_two] using h))

/-- The shifted polynomial remains irreducible over the p-adic field. -/
theorem shifted_irreducible_map :
    Irreducible ((shifted p).map (algebraMap ℤ_[p] ℚ_[p])) := by
  apply (shifted_monic p).irreducible_iff_irreducible_map_fraction_map.mp
  exact (shifted_isEisensteinAt p).irreducible inferInstance
    (shifted_monic p).isPrimitive (by rw [shifted_natDegree]; exact Nat.sub_pos_of_lt hp.out.one_lt)

/-- The prime cyclotomic polynomial is irreducible over the p-adic field. -/
theorem cyclotomic_irreducible : Irreducible (cyclotomic p ℚ_[p]) := by
  apply (MulEquiv.irreducible_iff (f := Polynomial.algEquivAevalXAddC (1 : ℚ_[p]))).mp
  change Irreducible ((cyclotomic p ℚ_[p]).comp (X + C 1))
  simpa only [shifted, Polynomial.map_comp, map_cyclotomic, Polynomial.map_add,
    map_X, Polynomial.map_one, C_1] using shifted_irreducible_map p

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] [Algebra ℤ_[p] E]
  [IsScalarTower ℤ_[p] ℚ_[p] E]

omit [IsScalarTower ℤ_[p] ℚ_[p] E] in
/-- A root of the shifted polynomial becomes a primitive root after adding one. -/
theorem isPrimitiveRoot_add_one {y : E} (hy : aeval y (shifted p) = 0) :
    IsPrimitiveRoot (y + 1) p := by
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[p] E).injective
  apply (isRoot_cyclotomic_iff_charZero hp.out.pos).mp
  change eval (y + 1) (cyclotomic p E) = 0
  simpa [shifted, aeval_def, eval₂_eq_eval_map, Polynomial.map_comp,
    map_cyclotomic, eval_comp] using hy

/-- The shifted polynomial is the minimal polynomial of each of its roots. -/
theorem minpoly_eq_shifted {y : E} (hy : aeval y (shifted p) = 0) :
    minpoly ℚ_[p] y = (shifted p).map (algebraMap ℤ_[p] ℚ_[p]) := by
  symm
  apply minpoly.eq_of_irreducible_of_monic (shifted_irreducible_map p) _
    ((shifted_monic p).map _)
  simpa only [aeval_map_algebraMap] using hy

omit [Algebra ℤ_[p] E] [IsScalarTower ℤ_[p] ℚ_[p] E] in
/-- The local cyclotomic degree in any presentation of the extension. -/
theorem cyclotomic_finrank [IsCyclotomicExtension {p} ℚ_[p] E] :
    Module.finrank ℚ_[p] E = p - 1 := by
  rw [IsCyclotomicExtension.finrank E (cyclotomic_irreducible p), Nat.totient_prime hp.out]

omit [Algebra ℤ_[p] E] [IsScalarTower ℤ_[p] ℚ_[p] E] in
/-- The minimal polynomial of a primitive root minus one over the p-adic field. -/
theorem minpoly_sub_one [IsCyclotomicExtension {p} ℚ_[p] E]
    {ζ : E} (hζ : IsPrimitiveRoot ζ p) :
    minpoly ℚ_[p] (ζ - 1) = (cyclotomic p ℚ_[p]).comp (X + 1) :=
  hζ.minpoly_sub_one_eq_cyclotomic_comp (cyclotomic_irreducible p)

/-- A concrete cyclotomic extension of the p-adic field, with its integral
closure, degree, ramification index and residue degree all constructed. -/
theorem exists_totallyRamified_cyclotomic :
    ∃ (E : Type) (_ : Field E) (_ : Algebra ℚ_[p] E) (_ : FiniteDimensional ℚ_[p] E)
      (_ : Algebra ℤ_[p] E) (_ : IsScalarTower ℤ_[p] ℚ_[p] E)
      (_ : IsCyclotomicExtension {p} ℚ_[p] E)
      (S : Type) (_ : CommRing S) (_ : IsDomain S) (_ : IsDiscreteValuationRing S)
      (_ : Algebra ℤ_[p] S) (_ : Module.Finite ℤ_[p] S) (_ : Algebra S E)
      (_ : IsScalarTower ℤ_[p] S E) (_ : IsFractionRing S E)
      (_ : IsIntegralClosure S ℤ_[p] E),
      Module.finrank ℚ_[p] E = p - 1 ∧
        (maximalIdeal S).ramificationIdx ℤ_[p] = p - 1 ∧
        (maximalIdeal S).inertiaDeg ℤ_[p] = 1 := by
  obtain ⟨E, instField, instAlgK, instFinite, instAlgR, instTowerK,
    S, instRing, instDomain, instDvr, instAlgS, instFiniteS, instAlgSE,
    instTowerS, instFraction, instClosure, y, hdeg, hy, hroot, hval, hgen⟩ :=
    (shifted_isEisensteinAt p).existsTotallyRamifiedExtension (K := ℚ_[p])
      (shifted_monic p) (by rw [shifted_natDegree]; exact Nat.sub_pos_of_lt hp.out.one_lt)
      PadicInt.irreducible_p
  have : FaithfulSMul ℤ_[p] S :=
    (faithfulSMul_iff_algebraMap_injective ℤ_[p] S).mpr <| by
      intro a b hab
      apply (IsFractionRing.injective ℤ_[p] ℚ_[p])
      apply (algebraMap ℚ_[p] E).injective
      simpa only [← IsScalarTower.algebraMap_apply] using congrArg (algebraMap S E) hab
  let z : E := algebraMap S E y
  have hz : aeval z (shifted p) = 0 := by
    rw [show z = (IsScalarTower.toAlgHom ℤ_[p] S E) y from rfl,
      aeval_algHom_apply, hroot, map_zero]
  have hzint : IsIntegral ℚ_[p] z := IsIntegral.of_finite ℚ_[p] z
  have hzgen : Algebra.adjoin ℚ_[p] {z} = ⊤ := by
    apply Subalgebra.toSubmodule_injective
    apply Submodule.eq_top_of_finrank_eq
    change Module.finrank ℚ_[p] (Algebra.adjoin ℚ_[p] {z}) = Module.finrank ℚ_[p] E
    rw [(Algebra.adjoin.powerBasis hzint).finrank,
      Algebra.adjoin.powerBasis_dim, minpoly_eq_shifted p hz,
      (shifted_monic p).natDegree_map, hdeg]
  have hzprim := isPrimitiveRoot_add_one p hz
  have hcycl : IsCyclotomicExtension {p} ℚ_[p] E := by
    apply (IsCyclotomicExtension.iff_singleton p ℚ_[p] E).mpr
    refine ⟨⟨z + 1, hzprim⟩, ?_⟩
    intro x
    have hle : Algebra.adjoin ℚ_[p] {z} ≤
        Algebra.adjoin ℚ_[p] {b : E | b ^ p = 1} := by
      apply Algebra.adjoin_le
      intro a ha
      rcases Set.mem_singleton_iff.mp ha with rfl
      have hmem := Algebra.subset_adjoin (R := ℚ_[p])
        (show z + 1 ∈ {b : E | b ^ p = 1} from hzprim.pow_eq_one)
      simpa using (Algebra.adjoin ℚ_[p] {b : E | b ^ p = 1}).sub_mem hmem
        (Subalgebra.one_mem _)
    exact hle (hzgen ▸ Algebra.mem_top)
  have he : (maximalIdeal S).ramificationIdx ℤ_[p] = p - 1 := by
    have heq := IsDiscreteValuationRing.addValMapUniformizerEqRamificationIdx
      (S := S) (π := (p : ℤ_[p])) PadicInt.irreducible_p
    rw [hval, shifted_natDegree] at heq
    exact_mod_cast heq.symm
  have hres : ∀ s : S, ∃ r : ℤ_[p],
      residue S (algebraMap ℤ_[p] S r) = residue S s := by
    intro s
    have hs : s ∈ Algebra.adjoin ℤ_[p] {y} := hgen ▸ Algebra.mem_top
    obtain ⟨f, hf⟩ := (Algebra.adjoin_singleton_eq_range_aeval ℤ_[p] y ▸ hs)
    refine ⟨f.coeff 0, ?_⟩
    have hyres : residue S y = 0 := (residue_eq_zero_iff _).mpr hy.not_isUnit
    rw [← hf]
    change _ = residue S (aeval y f)
    simp only [aeval_def, Polynomial.hom_eval₂, hyres]
    simp
  have hf : (maximalIdeal S).inertiaDeg ℤ_[p] = 1 := by
    rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal ℤ_[p]) (maximalIdeal S)]
    apply Module.finrank_of_bijective_algebraMap
    refine ⟨(algebraMap (ResidueField ℤ_[p]) (ResidueField S)).injective, ?_⟩
    intro x
    obtain ⟨s, rfl⟩ := residue_surjective (R := S) x
    obtain ⟨r, hr⟩ := hres s
    exact ⟨residue ℤ_[p] r, hr⟩
  exact ⟨E, instField, instAlgK, instFinite, instAlgR, instTowerK, hcycl,
    S, instRing, instDomain, instDvr, instAlgS, instFiniteS, instAlgSE,
    instTowerS, instFraction, instClosure, hdeg.trans (shifted_natDegree p), he, hf⟩

end LocalCyclotomic
