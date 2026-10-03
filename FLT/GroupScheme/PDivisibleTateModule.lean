/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleTateAction
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.NumberTheory.Padics.RingHoms

/-! # The p-adic module of coherent Tate sequences

Scalars act at level n through their actual residue modulo p^n.
Compatibility follows from the specified annihilation and reduction maps.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- Each finite level is a module over its annihilating residue ring. -/
instance instModuleZModPoints (n : ℕ) : Module (ZMod (p ^ n)) (X.level n).Points :=
  AddCommGroup.zmodModule (X.killed n)

/-- The finite-level p-adic action is reduction of scalars modulo p^n. -/
instance instModulePadicPoints (n : ℕ) : Module ℤ_[p] (X.level n).Points :=
  Module.compHom (X.level n).Points (PadicInt.toZModPow n)

/-- The finite-level action is explicitly the action of the residue. -/
theorem padic_smul_points (n : ℕ) (a : ℤ_[p]) (x : (X.level n).Points) :
    a • x = PadicInt.toZModPow n a • x := rfl

/-- Every actual reduction is linear for these p-adic actions. -/
theorem pointReduction_padic_smul {m n : ℕ} (h : m ≤ n) (a : ℤ_[p])
    (x : (X.level n).Points) :
    genericHom (X.reduction h) (a • x) = a • genericHom (X.reduction h) x := by
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
  rw [X.padic_smul_points, X.padic_smul_points, hn, hm,
    Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

/-- The coherent sequences form a submodule of the product of finite levels. -/
def tateSubmodule : Submodule ℤ_[p] (∀ n, (X.level n).Points) where
  __ := X.tateSequences
  smul_mem' a x hx := by
    intro m n h
    change genericHom (X.reduction h) (a • x n) = a • x m
    rw [X.pointReduction_padic_smul, hx h]

/-- The Tate inverse limit has its canonical p-adic module structure. -/
instance instModulePadicTate : Module ℤ_[p] X.tateSequences :=
  inferInstanceAs (Module ℤ_[p] X.tateSubmodule)

/-- Evaluation is linear over the p-adic integers. -/
def tateEvalLinear (n : ℕ) : X.tateSequences →ₗ[ℤ_[p]] (X.level n).Points where
  __ := X.tateEval n
  map_smul' _ _ := rfl

/-- Galois commutes with the canonical p-adic action. -/
instance instSMulCommClassTate :
    SMulCommClass (Field.absoluteGaloisGroup K) ℤ_[p] X.tateSequences where
  smul_comm g a x := by
    apply X.tate_ext
    intro n
    change g • (PadicInt.toZModPow n a • x.val n) =
      PadicInt.toZModPow n a • (g • x.val n)
    rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow n a),
      Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact smul_comm g _ _

end ThreeAdicPlan.PDivisibleSystem
