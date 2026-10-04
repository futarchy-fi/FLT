/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleTateCompact
public import Mathlib.LinearAlgebra.StdBasis

/-! # Continuous scalar evaluation on actual p-power torsion modules -/

@[expose] public noncomputable section
namespace ThreeAdicPlan
variable {p : ℕ} [Fact p.Prime] {R M : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] (e : R ≃+* ℤ_[p]) (n : ℕ)
  (hn : ∀ x : M, p ^ n • x = 0)

include hn in
/-- Equal p-power residues act identically on the original torsion module. -/
theorem torsion_smul_eq_of_padic_residue {a b : ℤ_[p]}
    (hab : PadicInt.toZModPow n a = PadicInt.toZModPow n b) (x : M) :
    e.symm a • x = e.symm b • x := by
  have hz : a - b ∈ RingHom.ker (PadicInt.toZModPow n) := by
    change PadicInt.toZModPow n (a - b) = 0
    rw [map_sub, hab, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hz
  have hd := map_dvd e.symm.toRingHom hz
  simp only [map_sub, map_pow, map_natCast] at hd
  obtain ⟨c, hc⟩ := hd
  change e.symm a - e.symm b = (p : R) ^ n * c at hc
  apply sub_eq_zero.mp
  rw [← sub_smul, hc, mul_smul, ← Nat.cast_pow,
    Nat.cast_smul_eq_nsmul, hn]

variable [TopologicalSpace M]

include n hn in
/-- Scalar evaluation is continuous through the actual finite residue map. -/
theorem continuous_torsion_scalar (x : M) :
    Continuous (fun a : ℤ_[p] ↦ e.symm a • x) := by
  have he : (fun a : ℤ_[p] ↦ e.symm a • x) =
      (fun z : ZMod (p ^ n) ↦ (z.val : R) • x) ∘ PadicInt.toZModPow n := by
    funext a
    have hres : PadicInt.toZModPow n a =
        PadicInt.toZModPow n ((PadicInt.toZModPow n a).val : ℤ_[p]) := by simp
    simpa only [map_natCast, Function.comp_apply] using
      torsion_smul_eq_of_padic_residue e n hn hres x
  rw [he]
  exact continuous_of_discreteTopology.comp (PDivisibleSystem.continuous_padicResidue n)

variable [DiscreteTopology M]

include n hn in
/-- Every map from a finite free original-base module is continuous in p-adic coordinates. -/
theorem continuous_torsion_linearMap {d : ℕ} (f : (Fin d → R) →ₗ[R] M) :
    Continuous (fun c : Fin d → ℤ_[p] ↦ f (fun i ↦ e.symm (c i))) := by
  let b := Pi.basisFun R (Fin d)
  have he (c : Fin d → ℤ_[p]) : f (fun i ↦ e.symm (c i)) =
      ∑ i, e.symm (c i) • f (b i) := by
    conv_lhs => rw [← b.sum_repr (fun i ↦ e.symm (c i))]
    simp only [map_sum, map_smul, b, Pi.basisFun_repr]
  simp_rw [he]
  apply continuous_finsetSum
  intro i _
  exact (continuous_torsion_scalar e n hn (f (b i))).comp (continuous_apply i)

end ThreeAdicPlan
