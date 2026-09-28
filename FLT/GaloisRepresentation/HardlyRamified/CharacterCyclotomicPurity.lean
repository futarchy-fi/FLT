/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.FiniteCharacterDual
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

/-!
# Cyclotomic purity from triviality of the character dual

A finite point group killed by `p^n` has its usual `ℤₚ` action through `ℤ/p^nℤ`.
If its full geometric character dual has trivial Galois action, character
separation and the defining roots-of-unity identity of the cyclotomic character
prove pointwise cyclotomic purity at that level.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- The usual `ℤₚ`-module structure on an abelian group killed by `p^n`. -/
abbrev primePowerModule {W : Type*} [AddCommGroup W] (p n : ℕ) [Fact p.Prime]
    (hkill : ∀ w : W, (p ^ n) • w = 0) : Module ℤ_[p] W := by
  letI := AddCommGroup.zmodModule hkill
  exact Module.compHom W (PadicInt.toZModPow n)

/-- Finite-level `ℤₚ` multiplication is multiplication by a representative
of the reduction modulo `p^n`. -/
theorem primePowerModule_smul {W : Type*} [AddCommGroup W] (p n : ℕ) [Fact p.Prime]
    (hkill : ∀ w : W, (p ^ n) • w = 0) (r : ℤ_[p]) (w : W) :
    letI := primePowerModule p n hkill
    r • w = (r.toZModPow n).val • w := by
  let := AddCommGroup.zmodModule hkill
  change (r.toZModPow n) • w = (r.toZModPow n).val • w
  have := Nat.cast_smul_eq_nsmul (ZMod (p ^ n)) (r.toZModPow n).val w
  simpa using this

namespace FiniteContinuousGaloisModule

/-- Triviality of the full character dual identifies the action at every
finite prime-power level with the actual cyclotomic character. -/
theorem cyclotomic_nsmul_of_characterDual_trivial (W : FiniteContinuousGaloisModule)
    (p n : ℕ) [Fact p.Prime] (hkill : ∀ w : W, (p ^ n) • w = 0)
    (hdual : Pure W.characterDual
      (1 : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℤ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (w : W) :
    σ • w =
      ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv).val.toZModPow n).val • w := by
  apply W.characters_separate
  intro φ
  let ψ : Additive W.Characters := Additive.ofMul φ
  have hφ : σ • ψ = ψ := by
    simpa using hdual σ ψ
  have he := W.characterDual_eval_smul σ ψ w
  rw [hφ] at he
  change φ (Multiplicative.ofAdd (σ • w)) = σ • φ (Multiplicative.ofAdd w) at he
  have hp : φ (Multiplicative.ofAdd w) ^ (p ^ n) = 1 := by
    rw [← map_pow, ← ofAdd_nsmul, hkill]
    exact map_one φ
  have hp' : (φ (Multiplicative.ofAdd w) : AlgebraicClosure ℚ) ^ (p ^ n) = 1 :=
    congrArg Units.val hp
  apply Units.ext
  rw [ofAdd_nsmul, map_pow]
  rw [he]
  exact cyclotomicCharacter.spec p σ.toRingEquiv _ hp'

/-- With its canonical finite-level `ℤₚ` action, a finite module whose character
dual is trivial has pointwise cyclotomic scalar action. -/
theorem pure_cyclotomic_of_characterDual_trivial (W : FiniteContinuousGaloisModule)
    (p n : ℕ) [Fact p.Prime] (hkill : ∀ w : W, (p ^ n) • w = 0)
    (hdual : Pure W.characterDual
      (1 : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℤ)) :
    letI := primePowerModule p n hkill
    Pure W (fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ ↦
      (cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv).val) := by
  let := primePowerModule p n hkill
  intro σ w
  rw [primePowerModule_smul]
  exact W.cyclotomic_nsmul_of_characterDual_trivial p n hkill hdual σ w

end FiniteContinuousGaloisModule
end ThreeAdicPlan
