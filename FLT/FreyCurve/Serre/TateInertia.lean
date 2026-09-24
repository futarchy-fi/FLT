/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.KnownIn1980s.EllipticCurves.TateCurve

/-!
# Inertia on split multiplicative torsion

Tate uniformization describes the deviation of a Galois automorphism on torsion
as a root of unity. The uniformization and its equivariance are existing admitted
inputs in `TateCurve`; the deductions here introduce no additional admissions.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine
open ValuativeRel

namespace WeierstrassCurve

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  (E : WeierstrassCurve k) [E.IsElliptic] [E.HasSplitMultiplicativeReduction 𝒪[k]]
  (Ω : Type*) [Field Ω] [Algebra k Ω]
  [DecidableEq Ω]

/-- Every torsion point has a Tate representative whose power is an integral power
of the Tate parameter. -/
theorem exists_tatePoint_of_nsmul_eq_zero {n : ℕ} (P : (E⁄Ω).Point)
    (hP : n • P = 0) :
    ∃ (u : Ωˣ) (m : ℤ), E.tatePoint Ω u = P ∧ u ^ n = E.qUnitSepClosure Ω ^ m := by
  obtain ⟨x, rfl⟩ := (E.tateEquivSepClosure Ω).surjective P
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
  have hx : Additive.ofMul (u : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) = x :=
    congrArg Additive.ofMul hu
  rw [← hx] at hP ⊢
  have hpow : (↑(u ^ n) : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) = 1 := by
    apply (E.tateEquivSepClosure Ω).injective
    rw [QuotientGroup.mk_pow]
    change E.tateEquivSepClosure Ω
      (n • Additive.ofMul (u : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) =
        E.tateEquivSepClosure Ω 0
    simpa only [map_nsmul, map_zero] using hP
  obtain ⟨m, hm⟩ := (QuotientGroup.eq_one_iff _).mp hpow
  exact ⟨u, m, rfl, hm.symm⟩

end WeierstrassCurve
