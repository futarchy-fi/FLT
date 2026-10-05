/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-! # The actual p-adic module of coherent geometric roots -/

@[expose] public noncomputable section
namespace ThreeAdicPlan
variable (L : Type*) [Field L] (p : ℕ) [Fact p.Prime]

/-- The additive finite root group at its original precision. -/
abbrev TateRootLevel (n : ℕ) := Additive (rootsOfUnity (p ^ n) L)

omit [Fact p.Prime] in
/-- The finite root group has its defining exponent. -/
theorem tateRootLevel_killed (n : ℕ) (x : TateRootLevel L p n) : p ^ n • x = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  exact x.toMul.property

instance tateRootLevelZMod (n : ℕ) : Module (ZMod (p ^ n)) (TateRootLevel L p n) :=
  AddCommGroup.zmodModule (tateRootLevel_killed L p n)

instance tateRootLevelPadic (n : ℕ) : Module ℤ_[p] (TateRootLevel L p n) :=
  Module.compHom _ (PadicInt.toZModPow n)

/-- Original root evaluation, written as an additive homomorphism. -/
def tateRootValue (n : ℕ) : TateRootLevel L p n →+ Additive Lˣ :=
  (rootsOfUnity (p ^ n) L).subtype.toAdditive

/-- A p-adic scalar acts by its finite residue exponent. -/
theorem tateRootValue_smul (n : ℕ) (a : ℤ_[p]) (x : TateRootLevel L p n) :
    tateRootValue L p n (a • x) = (PadicInt.toZModPow n a).val • tateRootValue L p n x := by
  change tateRootValue L p n (PadicInt.toZModPow n a • x) = _
  conv_lhs => rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow n a),
    Nat.cast_smul_eq_nsmul, map_nsmul]

/-- Reduction of roots is the prescribed power map. -/
def tateRootReduction {m n : ℕ} (h : m ≤ n) : TateRootLevel L p n →+ TateRootLevel L p m :=
  (show rootsOfUnity (p ^ n) L →* rootsOfUnity (p ^ m) L from
    { toFun := fun x ↦ ⟨x.val ^ (p ^ (n - m)), by
        rw [mem_rootsOfUnity, ← pow_mul, ← pow_add, Nat.sub_add_cancel h]
        exact x.property⟩
      map_one' := by apply Subtype.ext; exact one_pow _
      map_mul' := by intro x y; apply Subtype.ext; exact mul_pow _ _ _ }).toAdditive

/-- The original root transitions respect the canonical p-adic scalars. -/
theorem tateRootReduction_smul {m n : ℕ} (h : m ≤ n)
    (a : ℤ_[p]) (x : TateRootLevel L p n) :
    tateRootReduction L p h (a • x) = a • tateRootReduction L p h x := by
  let k := (PadicInt.toZModPow n a).val
  have hn : PadicInt.toZModPow n a = (k : ZMod (p ^ n)) :=
    (ZMod.natCast_zmod_val _).symm
  have hm : PadicInt.toZModPow m a = (k : ZMod (p ^ m)) := by
    have he := congrArg (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))) hn
    rw [map_natCast] at he
    change ((ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))).comp
      (PadicInt.toZModPow n)) a = _ at he
    rw [PadicInt.zmod_cast_comp_toZModPow m n h] at he
    exact he
  change tateRootReduction L p h (PadicInt.toZModPow n a • x) =
    PadicInt.toZModPow m a • tateRootReduction L p h x
  rw [hn, hm, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

/-- The actual cyclotomic root line before choosing any generator. -/
def tateRootSubmodule : Submodule ℤ_[p] (∀ n, TateRootLevel L p n) where
  carrier := {x | ∀ {m n} (h : m ≤ n), tateRootReduction L p h (x n) = x m}
  zero_mem' := by intro m n h; exact map_zero _
  add_mem' := by intro x y hx hy m n h; rw [Pi.add_apply, map_add, hx h, hy h]; rfl
  smul_mem' := by intro a x hx m n h; rw [Pi.smul_apply, tateRootReduction_smul, hx h]; rfl

/-- Coherent roots with their actual p-adic module structure. -/
abbrev TateRootModule := tateRootSubmodule L p

/-- The actual finite-root evaluation is linear. -/
def tateRootEval (n : ℕ) : TateRootModule L p →ₗ[ℤ_[p]] TateRootLevel L p n :=
  (LinearMap.proj n).comp (tateRootSubmodule L p).subtype

/-- Equality in the root line is detected by the original unit-valued roots. -/
@[ext] theorem tateRoot_ext {x y : TateRootModule L p}
    (h : ∀ n, tateRootValue L p n (tateRootEval L p n x) =
      tateRootValue L p n (tateRootEval L p n y)) : x = y := by
  apply Subtype.ext
  funext n
  exact Additive.toMul.injective (Subtype.ext (h n))
end ThreeAdicPlan
