/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LinearKummerClass

/-!
# The prime-field Kummer unit subspace

This subspace is the image of the independently defined valuation-unit
subgroup under the proved additive Kummer comparison.
-/

@[expose] public section

namespace KummerTheory

open GaloisRepresentation.Extensions

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {p : ℕ} [Fact p.Prime]
    (roots : ∀ q : Kˣ, ∃ b : Lˣ, b ^ p = Units.map (algebraMap K L) q)
    (A : ValuationSubring K)

/-- Valuation-unit classes form a prime-field subspace of continuous root cohomology. -/
noncomputable def primeUnitSubspace :
    Submodule (ZMod p) (LinearContinuousClass (ZMod p) Gal(L/K) (RootModule L p)) :=
  AddSubgroup.toZModSubmodule p
    ((unitClasses A p).toAddSubgroup.map (linearKummerEquiv roots).toAddMonoidHom)

/-- Membership is exactly the original valuation-unit condition on the Kummer parameter. -/
theorem mem_primeUnitSubspace_iff (x : LinearContinuousClass (ZMod p) Gal(L/K) (RootModule L p)) :
    x ∈ primeUnitSubspace roots A ↔
      IsUnitClass A p ((linearKummerEquiv roots).symm x).toMul := by
  change (∃ y : Additive (PowerClass K p), y.toMul ∈ unitClasses A p ∧
    linearKummerEquiv roots y = x) ↔ _
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [IsUnitClass, AddEquiv.symm_apply_apply] using hy
  · intro hx
    exact ⟨(linearKummerEquiv roots).symm x, hx, (linearKummerEquiv roots).apply_symm_apply x⟩

/-- The subspace criterion on any power class recovers independent unit membership. -/
theorem linearKummer_mem_primeUnitSubspace_iff (x : PowerClass K p) :
    linearKummerMap roots x ∈ primeUnitSubspace roots A ↔ IsUnitClass A p x := by
  rw [mem_primeUnitSubspace_iff]
  change IsUnitClass A p ((linearKummerEquiv roots).symm
    (linearKummerEquiv roots (Additive.ofMul x))).toMul ↔ _
  rw [AddEquiv.symm_apply_apply]
  rfl

end KummerTheory
