/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConstantRationalTateAction
public import FLT.GroupScheme.PDivisibleTateFree

/-! # The original constant Tate generator is an integral basis -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan.ConstantRationalPower
variable (p : ℕ) [Fact p.Prime] (hp : 2 < p)

/-- Scalar multiples of the original compatible constant generator. -/
def generatorLinear : ℤ_[p] →ₗ[ℤ_[p]] (system p hp).tateSequences :=
  (LinearMap.id : ℤ_[p] →ₗ[ℤ_[p]] ℤ_[p]).smulRight (generator p hp)

/-- The prescribed generator spans the first finite group over the original p-adic scalars. -/
theorem generatorLinear_first_surjective :
    Function.Surjective (((system p hp).tateEvalLinear 1).comp (generatorLinear p hp)) := by
  intro x
  obtain ⟨a, rfl⟩ := (points p 1).surjective x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨(a : ℤ_[p]), ?_⟩
  change (system p hp).tateEvalLinear 1 ((a : ℤ_[p]) • generator p hp) = _
  rw [Int.cast_smul_eq_zsmul, map_zsmul]
  change a • points p 1 (Ideal.Quotient.mk _ 1) = points p 1 (Ideal.Quotient.mk _ a)
  rw [← map_zsmul]
  congr 1
  simp [zsmul_eq_mul]

/-- Compactness promotes finite-level generation to the original full Tate module. -/
theorem generatorLinear_surjective : Function.Surjective (generatorLinear p hp) := by
  let g : (Fin 1 → ℤ_[p]) →ₗ[ℤ_[p]] (system p hp).tateSequences :=
    (generatorLinear p hp).comp (LinearMap.proj 0)
  have hg : ∀ n, Function.Surjective (((system p hp).tateEvalLinear n).comp g) := by
    apply (system p hp).tateEval_surjective_of_level_one
    intro a
    obtain ⟨c, hc⟩ := generatorLinear_first_surjective p hp a
    exact ⟨fun _ ↦ c, hc⟩
  intro x
  obtain ⟨c, hc⟩ := (system p hp).tateLift_surjective_of_levels g hg x
  exact ⟨c 0, hc⟩

/-- The same constant generator has no nonzero p-adic annihilator. -/
theorem generatorLinear_injective : Function.Injective (generatorLinear p hp) := by
  let : Module.IsTorsionFree ℤ_[p] (system p hp).tateSequences :=
    (system p hp).tateSequences_isTorsionFree
  exact smul_left_injective ℤ_[p] (generator_ne_zero p hp)

/-- The actual constant Tate module is Z_p, with one sent to its prescribed generator. -/
def constantTateEquiv : ℤ_[p] ≃ₗ[ℤ_[p]] (system p hp).tateSequences :=
  LinearEquiv.ofBijective (generatorLinear p hp)
    ⟨generatorLinear_injective p hp, generatorLinear_surjective p hp⟩

/-- The integral basis uses the original compatible residue classes of one. -/
theorem constantTateEquiv_one : constantTateEquiv p hp 1 = generator p hp := by
  change (1 : ℤ_[p]) • generator p hp = _
  exact one_smul _ _
end ThreeAdicPlan.ConstantRationalPower
