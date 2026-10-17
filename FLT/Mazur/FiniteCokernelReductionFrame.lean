/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCokernelReductionMatrix

/-!
# Constructing finite full error frames from finite cokernel submodules

Only a finite submodule of the cokernel must be supplied. Its divisibility
by the test ideal constructs the full ambient frame, matrix, correcting
vectors and initial expression. Ambient finiteness and Noetherianity are
not used. Divisibility itself remains an explicit geometric obligation.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteErrorReduction
variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (F : M →ₗ[R] N) (I : Ideal R)
set_option quotPrecheck false in
local notation "π" => (LinearMap.range F).mkQ
variable (Q : Submodule R (N ⧸ LinearMap.range F))

/-- Lift a finite generating frame of a cokernel submodule to the full target. -/
theorem exists_cokernel_frame (hQ : Q.FG) :
    ∃ (n : ℕ) (e : Fin n → N),
      Submodule.span R (Set.range (fun j ↦ π (e j))) = Q := by
  obtain ⟨n, q, hq⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hQ
  choose e he using fun j ↦ (LinearMap.range F).mkQ_surjective (q j)
  refine ⟨n, e, ?_⟩
  have h : (fun j ↦ π (e j)) = q := funext he
  rw [h, hq]

/-- Finite cokernel divisibility constructs the full finite reduction data. -/
theorem exists_full_reduction (hQ : Q.FG) (hred : Q ≤ I • Q)
    (y : N) (hy : π y ∈ Q) :
    ∃ (n : ℕ) (e : Fin n → N) (v : Fin n → M) (c : Fin n → Fin n → R)
      (z : M) (b : Fin n → R),
      (∀ j k, c j k ∈ I) ∧
      (∀ j, e j - F (v j) = ∑ k, c j k • e k) ∧
      y - F z = ∑ j, b j • e j := by
  obtain ⟨n, e, he⟩ := exists_cokernel_frame F Q hQ
  obtain ⟨v, c, hc, hv⟩ := exists_reduction_matrix F I e (by rwa [he])
  obtain ⟨z, b, hb⟩ := exists_initial_expression F e y (by rwa [he])
  exact ⟨n, e, v, c, z, b, hc, hv, hb⟩

/-- A finite divisible cokernel submodule gives an exact lift after one scalar near one. -/
theorem exists_lift_of_finite_cokernel (hQ : Q.FG) (hred : Q ≤ I • Q)
    (y : N) (hy : π y ∈ Q) :
    ∃ (a : R) (z : M), a - 1 ∈ I ∧ F z = a • y := by
  obtain ⟨n, e, v, c, z, b, hc, hv, hb⟩ := exists_full_reduction F I Q hQ hred y hy
  exact exists_lift_of_matrix F I e v c hc hv y z b hb

end FLT.Mazur.FiniteErrorReduction
