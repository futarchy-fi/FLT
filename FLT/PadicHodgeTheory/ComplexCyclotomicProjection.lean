/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexCyclotomicClosure

/-! # Continuous extensions of the actual cyclotomic normalized traces -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The actual trace on the algebraic union, followed by the original completion embedding. -/
def complexCyclotomicTraceMap (n : ℕ) : padicCyclotomicUnion p →ₗ[ℚ_[p]] ℂ_[p] :=
  (IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]).toLinearMap.comp
    ((padicCyclotomicProjection p (n + 1)).comp (padicCyclotomicUnion p).val.toLinearMap)

/-- The proved uniform bound is expressed in the norm of the actual closure. -/
theorem complexCyclotomicTraceMap_norm_le (n : ℕ) (x : padicCyclotomicUnion p) :
    ‖complexCyclotomicTraceMap p n x‖ ≤ p * ‖complexCyclotomicInclusion p x‖ := by
  change ‖((padicCyclotomicProjection p (n + 1) (x : PadicAlgCl p)) : ℂ_[p])‖ ≤ _
  rw [PadicComplex.norm_extends, complexCyclotomicInclusion_norm]
  exact padicCyclotomicProjection_union_norm_le p n x

/-- Extend the actual trace to the completed cyclotomic union. -/
def complexCyclotomicProjection (n : ℕ) : complexCyclotomicClosure p →L[ℚ_[p]] ℂ_[p] :=
  (complexCyclotomicTraceMap p n).extendOfNorm (complexCyclotomicInclusion p)

/-- Extension agrees with the original algebraic trace on every union element. -/
@[simp] theorem complexCyclotomicProjection_inclusion (n : ℕ) (x : padicCyclotomicUnion p) :
    complexCyclotomicProjection p n (complexCyclotomicInclusion p x) =
      ((padicCyclotomicProjection p (n + 1) (x : PadicAlgCl p)) : ℂ_[p]) :=
  LinearMap.extendOfNorm_eq (complexCyclotomicInclusion_dense p)
    ⟨p, complexCyclotomicTraceMap_norm_le p n⟩ x

/-- Every extended projection retains the same uniform bound. -/
theorem complexCyclotomicProjection_norm_le (n : ℕ) (x : complexCyclotomicClosure p) :
    ‖complexCyclotomicProjection p n x‖ ≤ p * ‖x‖ :=
  LinearMap.norm_extendOfNorm_apply_le (complexCyclotomicInclusion_dense p)
    p (complexCyclotomicTraceMap_norm_le p n) x

/-- Every algebraic union element is eventually fixed exactly by the projections. -/
theorem complexCyclotomicProjection_eventually_eq (x : padicCyclotomicUnion p) :
    ∃ N : ℕ, ∀ n ≥ N, complexCyclotomicProjection p n (complexCyclotomicInclusion p x) =
      ((x : PadicAlgCl p) : ℂ_[p]) := by
  obtain ⟨N, hN⟩ := (mem_padicCyclotomicUnion p x).mp x.property
  refine ⟨N, fun n hn ↦ ?_⟩
  have hx : (x : PadicAlgCl p) ∈ padicCyclotomicTower p (n + 1) :=
    padicCyclotomicTower_mono p (Nat.add_le_add_right hn 1) hN
  rw [complexCyclotomicProjection_inclusion, padicCyclotomicProjection_apply]
  exact congrArg (fun y : padicCyclotomicTower p (n + 1) ↦ ((y : PadicAlgCl p) : ℂ_[p]))
    (padicCyclotomicTrace_coe p (n + 1) ⟨x, hx⟩)

end PadicHodgeTheory
