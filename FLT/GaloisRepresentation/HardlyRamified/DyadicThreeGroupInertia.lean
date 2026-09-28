/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.TameInertiaCyclic
public import FLT.GaloisRepresentation.HardlyRamified.ThreeGroupConjugation
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Invariant.Galois

/-!
# Three-group inertia over a dyadic residue field

Over a two-element residue field, a residue extension with three-group Galois
group has no nontrivial three-power roots of unity. The uniformizer character
then kills tame inertia, while its two-group kernel kills the remaining inertia.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- A residue extension of `𝔽₂` with three-group Galois group has no nontrivial
three-power torsion in its unit group. -/
theorem residueUnit_eq_one_of_threeGroup
    {k l : Type*} [Field k] [Fintype k] [Field l] [Algebra k l]
    [Algebra.IsAlgebraic k l] (hk : Fintype.card k = 2)
    (hG : IsPGroup 3 Gal(l/k)) (u : lˣ) (n : ℕ) (hu : u ^ (3 ^ n) = 1) : u = 1 := by
  let φ := FiniteField.frobeniusAlgEquivOfAlgebraic k l
  obtain ⟨m, hm⟩ := hG φ
  have hpow : (u : l) ^ (2 ^ (3 ^ m)) = u := by
    have h := AlgEquiv.congr_fun hm (u : l)
    rw [AlgEquiv.coe_pow] at h
    simpa only [φ, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, hk,
      AlgEquiv.one_apply] using h
  have hunit : u ^ (2 ^ (3 ^ m)) = u := Units.ext hpow
  have hsub : u ^ (2 ^ (3 ^ m) - 1) = 1 := by
    have hle : 1 ≤ (2 : ℕ) ^ (3 ^ m) := Nat.one_le_pow _ _ (by decide)
    apply mul_left_cancel (a := u)
    rw [mul_one, ← pow_succ', Nat.sub_add_cancel hle, hunit]
  exact (pow_eq_one_iff_of_coprime
    ((coprime_three_two_pow_three_pow_sub_one m).pow_left n)).mp ⟨hu, hsub⟩

open IsLocalRing
open scoped Pointwise

/-- A finite three-group acting as a Galois group on a DVR over a local ring with
two-element residue field has trivial inertia. -/
theorem inertia_eq_bot_of_threeGroup_residue_two
    (A B G : Type*) [CommRing A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    (hG : IsPGroup 3 G) (hcard : Nat.card (ResidueField A) = 2) :
    (maximalIdeal B).inertia G = ⊥ := by
  let k := ResidueField A
  let l := ResidueField B
  let : Finite k := Nat.finite_of_card_ne_zero (by simp [k, hcard])
  let : Fintype k := Fintype.ofFinite k
  let : Normal k l := Ideal.Quotient.normal G (maximalIdeal A) (maximalIdeal B)
  have hk : Fintype.card k = 2 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have hres : IsPGroup 3 Gal(l/k) :=
    (hG.to_subgroup (MulAction.stabilizer G (maximalIdeal B))).of_surjective
      (Ideal.Quotient.stabilizerHom (maximalIdeal B) (maximalIdeal A) G)
      (Ideal.Quotient.stabilizerHom_surjective G (maximalIdeal A) (maximalIdeal B))
  let : CharP k 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by
    rw [← hk]
    exact FiniteField.cast_card_eq_zero k)
  let : CharP l 2 := charP_of_injective_ringHom (algebraMap k l).injective 2
  let : FaithfulSMul G B := IsGaloisGroup.faithful A
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  apply le_antisymm ?_ bot_le
  intro g hg
  change g = 1
  let t : (maximalIdeal B).inertia G := ⟨g, hg⟩
  obtain ⟨n, hn⟩ := (hG.to_subgroup ((maximalIdeal B).inertia G)) t
  have hχ : uniformizerCharacter hπ t = 1 :=
    residueUnit_eq_one_of_threeGroup hk hres _ n (by rw [← map_pow, hn, map_one])
  obtain ⟨m, hm⟩ := uniformizerCharacter_ker_isPGroup hπ Nat.prime_two ⟨t, hχ⟩
  have ht : t ^ (2 ^ m) = 1 := congrArg Subtype.val hm
  have hone : t = 1 := (pow_eq_one_iff_of_coprime
    (((by decide : Nat.Coprime 2 3).pow_left m).pow_right n)).mp ⟨ht, hn⟩
  exact congrArg Subtype.val hone

end ThreeAdicPlan
