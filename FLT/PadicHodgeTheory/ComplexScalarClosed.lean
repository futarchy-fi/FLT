/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexGaloisAction

/-! # Closedness of the standard Q_p scalars inside C_p -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Completeness of Q_p makes its actual image in C_p closed. -/
theorem complexScalar_isClosed : IsClosed (Set.range (algebraMap ℚ_[p] ℂ_[p])) :=
  (AddMonoidHomClass.isometry_of_norm (algebraMap ℚ_[p] ℂ_[p])
    (PadicComplex.norm_extends' p)).isClosedEmbedding.isClosed_range

/-- Arbitrarily close scalar approximants characterize the existing scalar image. -/
theorem complexScalar_mem_iff_approximation (x : ℂ_[p]) :
    x ∈ Set.range (algebraMap ℚ_[p] ℂ_[p]) ↔
      ∀ ε : ℝ, 0 < ε → ∃ a : ℚ_[p], ‖x - algebraMap ℚ_[p] ℂ_[p] a‖ < ε := by
  rw [← (complexScalar_isClosed p).closure_eq, Metric.mem_closure_iff]
  simp only [Set.mem_range, exists_exists_eq_and, dist_eq_norm]

/-- The completed action fixes the standard scalars. -/
theorem complexGalois_algebraMap (σ : PadicGalois p) (a : ℚ_[p]) :
    complexGalois p σ (algebraMap ℚ_[p] ℂ_[p] a) = algebraMap ℚ_[p] ℂ_[p] a := by
  change complexGalois p σ ((algebraMap ℚ_[p] (PadicAlgCl p) a : PadicAlgCl p) : ℂ_[p]) = _
  rw [complexGalois_coe, σ.commutes]
  rfl

/-- Scalar translation leaves every Galois displacement unchanged. -/
theorem complexGalois_displacement_sub_scalar (σ : PadicGalois p) (x : ℂ_[p]) (a : ℚ_[p]) :
    complexGalois p σ (x - algebraMap ℚ_[p] ℂ_[p] a) -
      (x - algebraMap ℚ_[p] ℂ_[p] a) = complexGalois p σ x - x := by
  rw [map_sub, complexGalois_algebraMap]
  ring

end PadicHodgeTheory
