/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexCyclotomicKernelDescent
public import FLT.PadicHodgeTheory.ComplexCyclotomicProjectionConvergence
public import FLT.PadicHodgeTheory.ComplexCyclotomicTraceInvariant
public import FLT.PadicHodgeTheory.ComplexTwistApproximation
public import FLT.PadicHodgeTheory.PadicCyclotomicTailCharacter

/-! # Nonzero integral twists of the original C_p have no invariants -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The actual embedding of p-adic units preserves detection of integer weights. -/
theorem padicUnit_zpow_coe_ne_one (u : ℤ_[p]ˣ) (k : ℤ) (hu : u ^ k ≠ 1) :
    (u.val : ℚ_[p]) ^ k ≠ 1 := by
  intro h
  apply hu
  apply Units.ext
  apply Subtype.ext
  let f : ℤ_[p]ˣ →* ℚ_[p] :=
    (Units.coeHom ℚ_[p]).comp (Units.map (algebraMap ℤ_[p] ℚ_[p]))
  exact (map_zpow f u k).trans h

/-- Every completed weighted invariant descends to the actual cyclotomic closure. -/
theorem complexTwist_fixed_mem_cyclotomicClosure (k : ℤ) (x : ℂ_[p])
    (hx : ∀ σ : PadicGalois p,
      (padicCyclotomicWeight p σ k : ℂ_[p]) * complexGalois p σ x = x) :
    x ∈ complexCyclotomicClosure p := by
  apply complexCyclotomic_kernel_fixed_mem_closure p x
  intro σ hσ
  have hw : padicCyclotomicWeight p σ k = 1 := by
    simp only [padicCyclotomicWeight, hσ, Units.val_one, PadicInt.coe_one, one_zpow, map_one]
  simpa only [hw, UniformSpace.Completion.coe_one, one_mul] using hx σ

/-- The actual normalized projection of a nonzero-weight invariant is zero at every level. -/
theorem complexTwist_fixed_projection_eq_zero (k : ℤ) (hk : k ≠ 0)
    (x : complexCyclotomicClosure p)
    (hx : ∀ σ : PadicGalois p,
      (padicCyclotomicWeight p σ k : ℂ_[p]) * complexGalois p σ (x : ℂ_[p]) = x)
    (n : ℕ) : complexCyclotomicProjection p n x = 0 := by
  obtain ⟨τ, hτ⟩ := padicCyclotomic_tail_character_zpow_ne_one p n k hk
  let σ := τ.restrictScalars ℚ_[p]
  let c : ℚ_[p] := ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val : ℚ_[p]) ^ k
  have hc : c ≠ 1 := padicUnit_zpow_coe_ne_one p _ k hτ
  have he : c • complexCyclotomicGalois p σ x = x := by
    apply Subtype.ext
    rw [Submodule.coe_smul, complexCyclotomicGalois_coe, Algebra.smul_def]
    exact hx σ
  have ht := congrArg (complexCyclotomicProjection p n) he
  rw [map_smul, complexCyclotomicProjection_relative_invariant p n τ x] at ht
  have hz : (c - 1) • complexCyclotomicProjection p n x = 0 := by
    rw [sub_smul, one_smul, ht, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc)

/-- Every nonzero integral cyclotomic twist of the original C_p has zero fixed space. -/
theorem complexTwist_fixed_eq_zero (k : ℤ) (hk : k ≠ 0) (x : ℂ_[p])
    (hx : ∀ σ : PadicGalois p,
      (padicCyclotomicWeight p σ k : ℂ_[p]) * complexGalois p σ x = x) : x = 0 := by
  let y : complexCyclotomicClosure p := ⟨x, complexTwist_fixed_mem_cyclotomicClosure p k x hx⟩
  have hz : ∀ n, complexCyclotomicProjection p n y = 0 :=
    complexTwist_fixed_projection_eq_zero p k hk y hx
  have ht := complexCyclotomicProjection_tendsto p y
  simp only [hz] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

end PadicHodgeTheory
