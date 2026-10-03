/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.PadicGaloisOrbit

/-! # The degree-dependent algebraic Galois averaging estimate

The inverse norm of the orbit cardinality is essential in this estimate.
It is not a uniform Ax bound as the algebraic element varies.
-/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The actual normalized sum of distinct algebraic conjugates. -/
def padicGaloisAverage (a : PadicAlgCl p) : PadicAlgCl p :=
  (Fintype.card (MulAction.orbit (PadicGalois p) a) : PadicAlgCl p)⁻¹ *
    padicGaloisOrbitSum p a

/-- The normalized orbit sum is a standard Q_p scalar. -/
theorem padicGaloisAverage_mem_range (a : PadicAlgCl p) :
    padicGaloisAverage p a ∈ Set.range (algebraMap ℚ_[p] (PadicAlgCl p)) := by
  apply (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
  intro σ
  simp only [padicGaloisAverage, map_mul, map_inv₀, map_natCast, padicGaloisOrbitSum_fixed]

/-- Subtracting the original point expresses the error as an average of displacements. -/
theorem padicGaloisAverage_sub (a : PadicAlgCl p) :
    padicGaloisAverage p a - a =
      (Fintype.card (MulAction.orbit (PadicGalois p) a) : PadicAlgCl p)⁻¹ *
        ∑ b : MulAction.orbit (PadicGalois p) a, ((b : PadicAlgCl p) - a) := by
  have hn : (Fintype.card (MulAction.orbit (PadicGalois p) a) : PadicAlgCl p) ≠ 0 :=
    Nat.cast_ne_zero.mpr (padicGalois_orbit_card_pos p a).ne'
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_sub, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  rfl

/-- The ultrametric averaging estimate retains the exact orbit-cardinality loss. -/
theorem padicGaloisAverage_sub_le (a : PadicAlgCl p) {r : ℝ} (hr : 0 ≤ r)
    (ha : ∀ σ : PadicGalois p, ‖σ a - a‖ ≤ r) :
    ‖padicGaloisAverage p a - a‖ ≤
      ‖(Fintype.card (MulAction.orbit (PadicGalois p) a) : PadicAlgCl p)‖⁻¹ * r := by
  rw [padicGaloisAverage_sub, norm_mul, norm_inv]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (norm_nonneg _))
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr
  intro b _
  obtain ⟨σ, hσ⟩ := b.property
  simpa only [← hσ, AlgEquiv.smul_def] using ha σ

/-- The estimate provides an actual scalar witness, with its degree loss explicit. -/
theorem padicGalois_exists_scalar_approximation (a : PadicAlgCl p) {r : ℝ} (hr : 0 ≤ r)
    (ha : ∀ σ : PadicGalois p, ‖σ a - a‖ ≤ r) :
    ∃ b : ℚ_[p], ‖a - algebraMap ℚ_[p] (PadicAlgCl p) b‖ ≤
      ‖(Fintype.card (MulAction.orbit (PadicGalois p) a) : PadicAlgCl p)‖⁻¹ * r := by
  obtain ⟨b, hb⟩ := padicGaloisAverage_mem_range p a
  refine ⟨b, ?_⟩
  rw [hb, norm_sub_rev]
  exact padicGaloisAverage_sub_le p a hr ha

end PadicHodgeTheory
