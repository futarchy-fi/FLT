/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.AbsIrredAdapter
public import FLT.GaloisRepresentation.HardlyRamified.Defs
public import FLT.GaloisRepresentation.HardlyRamified.RationalComplexConjugation
public import FLT.GaloisRepresentation.HardlyRamified.ResidualCharacteristic

/-! # Absolute irreducibility of residual hardly ramified representations -/

@[expose] public noncomputable section

open Module

universe u

namespace LinearMap

/-- A determinant-minus-one involution in dimension two has a one-dimensional
fixed space whenever minus one differs from one. -/
theorem finrank_fixed_of_involutive_det_neg_one
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f : V →ₗ[k] V) (hV : finrank k V = 2) (hi : Function.Involutive f)
    (hd : f.det = -1) (hne : (-1 : k) ≠ 1) :
    finrank k (Module.End.eigenspace f 1) = 1 := by
  have hb : Module.End.eigenspace f 1 ≠ ⊥ := by
    intro hb
    have hf : f = (-1 : k) • (LinearMap.id : V →ₗ[k] V) := by
      ext x
      have hx : f x + x ∈ Module.End.eigenspace f 1 := by
        rw [Module.End.mem_eigenspace_iff]
        simp only [map_add, hi x, one_smul]
        exact add_comm _ _
      rw [hb, Submodule.mem_bot] at hx
      simpa using eq_neg_of_add_eq_zero_left hx
    apply hne
    rw [← hd, hf, det_smul, hV, det_id]
    ring
  have ht : Module.End.eigenspace f 1 ≠ ⊤ := by
    intro ht
    have hf : f = LinearMap.id := by
      ext x
      have hx : x ∈ Module.End.eigenspace f 1 := by rw [ht]; trivial
      simpa only [Module.End.mem_eigenspace_iff, one_smul, LinearMap.id_apply] using hx
    exact hne (hd.symm.trans (hf ▸ det_id))
  have hpos := (Submodule.finrank_eq_zero (S := Module.End.eigenspace f 1)).not.mpr hb
  have hlt := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr ht)
  rw [finrank_top, hV] at hlt
  omega

end LinearMap

namespace GaloisRepresentation.IsHardlyRamified

open ThreeAdicPlan

variable {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
  {k V : Type*} [Field k] [Finite k] [TopologicalSpace k] [IsTopologicalRing k]
  [Algebra ℤ_[p] k] [AddCommGroup V] [Module k V] [Module.Finite k V]
  (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}

/-- The complex-conjugation fixed space follows from the cyclotomic determinant;
it is not an extra lifting hypothesis. -/
theorem complexConjugation_fixed_finrank (hρ : IsHardlyRamified hpodd hV ρ) :
    finrank k (Module.End.eigenspace (ρ.toRepresentation rationalComplexConjugation) 1) = 1 := by
  let _char := charP_of_finite_padic_algebra p k
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    obtain ⟨a, ha⟩ := hpodd
    omega
  have htwo : (2 : k) ≠ 0 := by
    intro h
    have hdiv := (CharP.cast_eq_zero_iff k p 2).mp h
    have := Nat.le_of_dvd (by decide : 0 < 2) hdiv
    omega
  have hne : (-1 : k) ≠ 1 := by
    intro h
    apply htwo
    have hh := congrArg (fun x : k ↦ x + 1) h
    simpa only [neg_add_cancel, one_add_one_eq_two] using hh.symm
  apply LinearMap.finrank_fixed_of_involutive_det_neg_one
    (ρ.toRepresentation rationalComplexConjugation) (Module.finrank_eq_of_rank_eq hV)
  · intro x
    have h : ρ.toRepresentation rationalComplexConjugation *
        ρ.toRepresentation rationalComplexConjugation = 1 := by
      rw [← map_mul, rationalComplexConjugation_mul_self, map_one]
    exact congrArg (fun f : Module.End k V ↦ f x) h
  · have hd := hρ.det rationalComplexConjugation
    change LinearMap.det (ρ.toRepresentation rationalComplexConjugation) = _ at hd
    simpa only [rationalComplexConjugation_cyclotomic, map_neg, map_one] using hd
  · exact hne

/-- Every irreducible residual hardly ramified representation is absolutely
irreducible, as required by deformation representability. -/
theorem isAbsolutelyIrreducible (hρ : IsHardlyRamified hpodd hV ρ)
    (hirr : ρ.IsIrreducible) : ρ.toRepresentation.IsAbsolutelyIrreducible.{u} :=
  GaloisRep.absIrred_of_rank_one_fixed_space ρ hirr
    (complexConjugation_fixed_finrank hpodd hV hρ)

end GaloisRepresentation.IsHardlyRamified
