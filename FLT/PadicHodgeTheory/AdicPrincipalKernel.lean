/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # Lifting a genuine mod-r generator of a saturated ideal -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable {R : Type*} [CommRing R]

/-- A submodule of an adically separated module is adically separated. -/
theorem adicHausdorff_submodule (I : Ideal R) {M : Type*} [AddCommGroup M] [Module R M]
    [IsHausdorff I M] (N : Submodule R M) : IsHausdorff I N := by
  constructor
  intro x hx
  apply Subtype.ext
  apply IsHausdorff.haus' (I := I)
  intro n
  apply SModEq.zero.mpr
  exact (Submodule.smul_mono le_rfl le_top)
    ((Submodule.mem_smul_top_iff (I ^ n) N x).mp (SModEq.zero.mp (hx n)))

/-- An actual one-step decomposition lifts to principality by adic completeness.
The remainder must remain in J; divisibility in the ambient ring alone does not suffice. -/
theorem ideal_eq_span_of_adic_decomposition (r ξ : R) (J : Ideal R)
    [IsPrecomplete (Ideal.span {r}) R] [IsHausdorff (Ideal.span {r}) R]
    (hξ : ξ ∈ J) (hstep : ∀ x ∈ J, ∃ a y, y ∈ J ∧ x = ξ * a + r * y) :
    J = Ideal.span {ξ} := by
  let I : Ideal R := Ideal.span {r}
  let : IsHausdorff I J := adicHausdorff_submodule I J
  let f : R →ₗ[R] J := LinearMap.toSpanSingleton R J ⟨ξ, hξ⟩
  have hf : Function.Surjective f := by
    apply surjective_of_mkQ_comp_surjective (I := I)
    intro z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (I • (⊤ : Submodule R J)) z
    obtain ⟨a, y, hy, h⟩ := hstep x x.property
    refine ⟨a, ?_⟩
    change Submodule.Quotient.mk (f a) = Submodule.Quotient.mk x
    apply Eq.symm
    apply (Submodule.Quotient.eq _).mpr
    have he : x - f a = r • (⟨y, hy⟩ : J) := by
      apply Subtype.ext
      change (x : R) - a * ξ = r * y
      rw [h]
      ring
    rw [he]
    exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton r))
      (Submodule.mem_top : (⟨y, hy⟩ : J) ∈ ⊤)
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha⟩ := hf ⟨x, hx⟩
    apply Ideal.mem_span_singleton.mpr
    refine ⟨a, ?_⟩
    have h := congrArg Subtype.val ha
    change a * ξ = x at h
    exact h.symm.trans (mul_comm a ξ)
  · rw [Ideal.span_singleton_le_iff_mem]
    exact hξ

end PadicHodgeTheory
