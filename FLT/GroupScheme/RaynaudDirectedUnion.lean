/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Directed
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Directed unions of DVR stages with a common uniformizer

A directed family of embedded DVRs with the same base uniformizer has a DVR
as its union. Constructing the directed family of unramified stages is a
separate obligation.
-/

@[expose] public noncomputable section

namespace RaynaudParameters

variable {R Ω ι : Type*} [CommRing R] [CommRing Ω] [IsDomain Ω]
  [Algebra R Ω] [Nonempty ι] (S : ι → Subalgebra R Ω)
  (hS : Directed (· ≤ ·) S)

include hS

omit [IsDomain Ω] in
/-- An element of the directed supremum comes from one stage. -/
theorem exists_stage_of_mem_iSup (x : ↥(⨆ i, S i)) : ∃ i, (x : Ω) ∈ S i := by
  have hx := x.property
  rw [← SetLike.mem_coe, Subalgebra.coe_iSup_of_directed hS, Set.mem_iUnion] at hx
  exact hx

omit [IsDomain Ω] in
/-- A unit in the union already has its inverse at some larger stage. -/
theorem isUnit_in_iSup_iff (i : ι) (x : S i) :
    IsUnit (Subalgebra.inclusion (le_iSup S i) x) ↔
      ∃ j, ∃ hij : S i ≤ S j, IsUnit (Subalgebra.inclusion hij x) := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨k, hk⟩ := exists_stage_of_mem_iSup S hS (↑u⁻¹)
    obtain ⟨j, hij, hkj⟩ := hS i k
    refine ⟨j, hij, isUnit_iff_exists_inv.mpr ⟨⟨_, hkj hk⟩, ?_⟩⟩
    apply Subtype.ext
    have h := congrArg (fun z : ↥(⨆ i, S i) ↦ (z : Ω)) u.val_inv
    simpa only [Units.inv_eq_val_inv, hu, Subalgebra.coe_mul,
      Subalgebra.coe_one, Subalgebra.coe_inclusion] using h
  · rintro ⟨j, hij, hj⟩
    exact hj.map (Subalgebra.inclusion (le_iSup S j))

omit [IsDomain Ω] in
/-- The common uniformizer stays irreducible in the directed union. -/
theorem irreducible_in_iSup (π : R)
    (hπ : ∀ i, Irreducible (algebraMap R (S i) π)) :
    Irreducible (algebraMap R (↥(⨆ i, S i)) π) := by
  have hn : ¬ IsUnit (algebraMap R (↥(⨆ i, S i)) π) := by
    intro hu
    let i : ι := Classical.arbitrary ι
    have hu' : IsUnit (Subalgebra.inclusion (le_iSup S i) (algebraMap R (S i) π)) := hu
    obtain ⟨j, hij, hj⟩ := (isUnit_in_iSup_iff S hS i _).mp hu'
    exact (hπ j).not_isUnit (by simpa using hj)
  refine ⟨hn, ?_⟩
  intro x y hxy
  obtain ⟨i, hi⟩ := exists_stage_of_mem_iSup S hS x
  obtain ⟨j, hj⟩ := exists_stage_of_mem_iSup S hS y
  obtain ⟨k, hik, hjk⟩ := hS i j
  let xk : S k := ⟨x, hik hi⟩
  let yk : S k := ⟨y, hjk hj⟩
  have hk : algebraMap R (S k) π = xk * yk :=
    Subtype.ext (congrArg (fun z : ↥(⨆ i, S i) ↦ (z : Ω)) hxy)
  rcases (hπ k).isUnit_or_isUnit hk with hx | hy
  · exact Or.inl (hx.map (Subalgebra.inclusion (le_iSup S k)))
  · exact Or.inr (hy.map (Subalgebra.inclusion (le_iSup S k)))

/-- Directed unions of DVR stages preserving a base uniformizer are DVRs. -/
theorem isDiscreteValuationRing_iSup [∀ i, IsDiscreteValuationRing (S i)] (π : R)
    (hπ : ∀ i, Irreducible (algebraMap R (S i) π)) :
    IsDiscreteValuationRing (↥(⨆ i, S i)) := by
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨algebraMap R _ π, irreducible_in_iSup S hS π hπ, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := exists_stage_of_mem_iSup S hS x
  let xi : S i := ⟨x, hi⟩
  have hxi : xi ≠ 0 := fun h ↦ hx
    (Subtype.ext (congrArg (fun z : S i ↦ (z : Ω)) h))
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hxi (hπ i)
  refine ⟨n, ?_⟩
  let f := Subalgebra.inclusion (le_iSup S i)
  refine ⟨Units.map f.toMonoidHom u, ?_⟩
  apply Subtype.ext
  have hh := congrArg (fun z : S i ↦ (z : Ω)) hu
  simpa [f, xi, mul_comm] using hh.symm

/-- The inclusions of the stages in this union are local homomorphisms. -/
theorem isLocalHom_inclusion_iSup [∀ i, IsDiscreteValuationRing (S i)] (π : R)
    (hπ : ∀ i, Irreducible (algebraMap R (S i) π)) (i : ι) :
    IsLocalHom (Subalgebra.inclusion (le_iSup S i)) := by
  let f := Subalgebra.inclusion (le_iSup S i)
  refine ⟨fun x hx ↦ ?_⟩
  have hx0 : x ≠ 0 := fun h ↦ hx.ne_zero (by rw [h, map_zero])
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 (hπ i)
  by_cases hn : n = 0
  · simp [hn]
  have hpow : IsUnit ((algebraMap R (↥(⨆ i, S i)) π) ^ n) := by
    have hh := isUnit_of_mul_isUnit_right (show IsUnit
      (f (u : S i) * (f (algebraMap R (S i) π)) ^ n) from by
        simpa only [map_mul, map_pow] using hx)
    simpa using hh
  exact ((irreducible_in_iSup S hS π hπ).not_isUnit ((isUnit_pow_iff hn).mp hpow)).elim

end RaynaudParameters
