/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Ring.Compact

/-!
# Openness of p-power ideals in finite free p-adic algebras

In a finite basis, divisibility by p^n is coordinatewise divisibility.
The principal p-power ideal is therefore the inverse image of a finite
product of open ideals of the p-adic integers.
-/

@[expose] public section

namespace PadicInt

variable (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A]
  [Algebra ℤ_[p] A] [Module.Finite ℤ_[p] A] [Module.Free ℤ_[p] A]
  [TopologicalSpace A] [IsModuleTopology ℤ_[p] A]

/-- Principal p-power ideals are open in a finite free p-adic algebra. -/
theorem isOpen_span_p_pow (n : ℕ) :
    IsOpen (Ideal.span {(p : A) ^ n} : Set A) := by
  classical
  let ι := Module.Free.ChooseBasisIndex ℤ_[p] A
  let : Fintype ι := Module.Free.ChooseBasisIndex.fintype ℤ_[p] A
  let e : A ≃L[ℤ_[p]] (ι → ℤ_[p]) :=
    IsModuleTopology.continuousLinearEquiv (Module.Free.chooseBasis ℤ_[p] A).equivFun
  have hopen : IsOpen (Ideal.span {(p : ℤ_[p]) ^ n} : Set ℤ_[p]) := by
    simpa only [maximalIdeal_eq_span_p, Ideal.span_singleton_pow] using
      IsLocalRing.isOpen_maximalIdeal_pow ℤ_[p] n
  have heq : (Ideal.span {(p : A) ^ n} : Set A) =
      e ⁻¹' Set.pi Set.univ (fun _ : ι ↦ (Ideal.span {(p : ℤ_[p]) ^ n} : Set ℤ_[p])) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const,
      SetLike.mem_coe, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, rfl⟩ i
      refine ⟨e y i, ?_⟩
      have h := congrFun (e.map_smul ((p : ℤ_[p]) ^ n) y) i
      simpa only [Algebra.smul_def, map_pow, map_natCast, Pi.smul_apply,
        smul_eq_mul] using h
    · intro h
      choose c hc using h
      refine ⟨e.symm c, ?_⟩
      apply e.injective
      have hs := e.map_smul ((p : ℤ_[p]) ^ n) (e.symm c)
      simp only [Algebra.smul_def, map_pow, map_natCast, e.apply_symm_apply] at hs
      rw [hs]
      exact funext fun i ↦ hc i
  rw [heq]
  exact (isOpen_set_pi Set.finite_univ fun _ _ ↦ hopen).preimage e.continuous

end PadicInt
