/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexGaloisAction
public import Mathlib.Topology.Algebra.MulAction

/-! # Joint continuity of the Galois action on C_p -/

@[expose] public noncomputable section
open scoped Topology
open Filter UniformSpace
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- An algebraic orbit is locally constant for the Krull topology. -/
theorem padicGalois_eventually_eq (σ : PadicGalois p) (a : PadicAlgCl p) :
    ∀ᶠ τ in 𝓝 σ, τ a = σ a := by
  have h := (stabilizer_isOpen_of_isIntegral (K := ℚ_[p]) a).mem_nhds
    (show (1 : PadicGalois p) ∈ MulAction.stabilizer (PadicGalois p) a from
      (MulAction.stabilizer _ _).one_mem)
  have hc : Tendsto (fun τ : PadicGalois p ↦ σ⁻¹ * τ) (𝓝 σ) (𝓝 1) := by
    simpa only [Pi.mul_def, id_eq, inv_mul_cancel] using
      ((continuous_const : Continuous (fun _ : PadicGalois p ↦ σ⁻¹)).mul
        continuous_id).tendsto σ
  filter_upwards [hc h] with τ hτ
  change σ⁻¹ (τ a) = a at hτ
  simpa using congrArg σ hτ

/-- Density and the uniform isometry bound give continuity in both variables. -/
theorem complexGalois_continuous :
    Continuous (fun z : PadicGalois p × ℂ_[p] ↦ complexGalois p z.1 z.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨σ, x⟩
  rw [Metric.continuousAt_iff']
  intro ε hε
  obtain ⟨a, ha⟩ := Completion.denseRange_coe.exists_dist_lt x (by positivity : 0 < ε / 3)
  have heq : ∀ᶠ z : PadicGalois p × ℂ_[p] in 𝓝 (σ, x), z.1 a = σ a :=
    (continuous_fst.tendsto (σ, x)).eventually (padicGalois_eventually_eq p σ a)
  have hdist : ∀ᶠ z : PadicGalois p × ℂ_[p] in 𝓝 (σ, x), dist z.2 x < ε / 3 :=
    (continuous_snd.tendsto (σ, x)).eventually (Metric.ball_mem_nhds x (by positivity))
  filter_upwards [heq, hdist] with z hz hd
  have he : complexGalois p z.1 (a : ℂ_[p]) = complexGalois p σ (a : ℂ_[p]) := by
    simp only [complexGalois_coe, hz]
  calc
    dist (complexGalois p z.1 z.2) (complexGalois p σ x) ≤
        dist (complexGalois p z.1 z.2) (complexGalois p z.1 (a : ℂ_[p])) +
        dist (complexGalois p z.1 (a : ℂ_[p])) (complexGalois p σ x) := dist_triangle _ _ _
    _ = dist z.2 (a : ℂ_[p]) + dist (a : ℂ_[p]) x := by
      rw [(complexGalois_isometry p z.1).dist_eq, he,
        (complexGalois_isometry p σ).dist_eq]
    _ ≤ dist z.2 x + dist x (a : ℂ_[p]) + dist (a : ℂ_[p]) x :=
      add_le_add (dist_triangle _ _ _) le_rfl
    _ < ε := by rw [dist_comm x] at *; linarith

/-- The actual completed action is jointly continuous. -/
instance instContinuousSMulComplex : ContinuousSMul (PadicGalois p) ℂ_[p] :=
  ⟨complexGalois_continuous p⟩

end PadicHodgeTheory
