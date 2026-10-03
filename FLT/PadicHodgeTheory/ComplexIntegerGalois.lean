/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexGaloisContinuity
public import FLT.PadicHodgeTheory.ComplexIntegerAdic

/-! # The continuous Galois action on the actual integer ring of C_p -/

@[expose] public noncomputable section
open scoped NNReal
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Galois automorphisms preserve the completed valuation. -/
theorem complexGalois_valuation (σ : PadicGalois p) (x : ℂ_[p]) :
    Valued.v (complexGalois p σ x) = (Valued.v x : ℝ≥0) := by
  apply NNReal.eq
  simp only [complex_valuation_coe, complexGalois_norm]

/-- The completed Galois action restricts to the actual valuation ring. -/
def complexIntegerGalois (σ : PadicGalois p) : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p] where
  toFun x := ⟨complexGalois p σ x, by
    change Valued.v (complexGalois p σ x) ≤ (1 : ℝ≥0)
    rw [complexGalois_valuation]
    exact x.property⟩
  map_one' := Subtype.ext (map_one _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)

/-- The inclusion in C_p intertwines the two actions. -/
@[simp] theorem complexIntegerGalois_coe (σ : PadicGalois p) (x : 𝓞_ℂ_[p]) :
    (complexIntegerGalois p σ x : ℂ_[p]) = complexGalois p σ x := rfl

/-- Restriction respects the identity. -/
@[simp] theorem complexIntegerGalois_one (x : 𝓞_ℂ_[p]) :
    complexIntegerGalois p 1 x = x := by
  apply Subtype.ext
  simp

/-- Restriction respects multiplication in the Galois group. -/
theorem complexIntegerGalois_mul (σ τ : PadicGalois p) (x : 𝓞_ℂ_[p]) :
    complexIntegerGalois p (σ * τ) x =
      complexIntegerGalois p σ (complexIntegerGalois p τ x) := by
  apply Subtype.ext
  exact congrArg (fun f : ℂ_[p] →+* ℂ_[p] ↦ f x) (complexGalois_mul p σ τ)

/-- The integer-ring action preserves ring operations. -/
instance instMulSemiringActionComplexInteger :
    MulSemiringAction (PadicGalois p) 𝓞_ℂ_[p] where
  smul σ x := complexIntegerGalois p σ x
  one_smul := complexIntegerGalois_one p
  mul_smul := complexIntegerGalois_mul p
  smul_zero σ := map_zero (complexIntegerGalois p σ)
  smul_add σ := map_add (complexIntegerGalois p σ)
  smul_one σ := map_one (complexIntegerGalois p σ)
  smul_mul σ := map_mul (complexIntegerGalois p σ)

/-- Joint continuity descends to the integer ring with its subspace topology. -/
instance instContinuousSMulComplexInteger : ContinuousSMul (PadicGalois p) 𝓞_ℂ_[p] where
  continuous_smul :=
    ((complexGalois_continuous p).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

end PadicHodgeTheory
