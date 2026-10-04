/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantPowerResidues

/-! # Characters of integer residues from actual torsion units -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.ConstantPower
variable (p : ℕ) {U : Type*} [CommGroup U]

/-- The integer residue ring is the corresponding ZMod ring. -/
def residueZMod (n : ℕ) : Residue p n ≃+* ZMod (p ^ n) :=
  (Int.quotientSpanEquivZMod ((p : ℤ) ^ n)).trans (ZMod.ringEquivCongr (by simp))

/-- A root with the prescribed order defines an additive character on the residue group. -/
def rootCharacter (n : ℕ) (u : U) (hu : u ^ (p ^ n) = 1) : Residue p n →+ Additive U :=
  (ZMod.lift (p ^ n) ⟨zmultiplesHom (Additive U) (Additive.ofMul u), by
    change Additive.ofMul (u ^ ((p ^ n : ℕ) : ℤ)) = 0
    rw [zpow_natCast, hu]
    rfl⟩).comp (residueZMod p n).toAddMonoidHom

/-- The character evaluates integer representatives by their genuine integer powers. -/
theorem rootCharacter_mk (n : ℕ) (u : U) (hu : u ^ (p ^ n) = 1) (a : ℤ) :
    rootCharacter p n u hu (Ideal.Quotient.mk _ a) = Additive.ofMul (u ^ a) := by
  have he : (residueZMod p n).toAddMonoidHom (Ideal.Quotient.mk _ a) =
      (a : ZMod (p ^ n)) := map_intCast (residueZMod p n) a
  unfold rootCharacter
  rw [AddMonoidHom.comp_apply, he, ZMod.lift_coe]
  rfl

/-- Restriction along the original inclusion is the transition power of the root. -/
theorem rootCharacter_embed {m n : ℕ} (h : m ≤ n) (u v : U)
    (hu : u ^ (p ^ n) = 1) (hv : v ^ (p ^ m) = 1)
    (he : u ^ (p ^ (n - m)) = v) (a : Residue p m) :
    rootCharacter p n u hu (embed p h a) = rootCharacter p m v hv a := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [embed_mk, rootCharacter_mk, rootCharacter_mk, zpow_mul, ← Nat.cast_pow,
    zpow_natCast, he]

end ThreeAdicPlan.ConstantPower
