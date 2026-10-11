/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Bases from distinct exact filtration orders

Nonzero vectors with strictly increasing exact orders are independent.
When their number equals the dimension of a containing filtration piece,
the same vectors form a basis of that piece.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FilteredPoleBasis
open Module
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
  (P : ℕ → Submodule k V) (hP : Monotone P)

include hP in
/-- Distinct increasing exact filtration orders imply linear independence. -/
theorem linearIndependent_of_orders (N : ℕ) (v : Fin N → V) (d : Fin N → ℕ)
    (hd : StrictMono d) (hv : ∀ i, v i ∈ P (d i)) (hz : ∀ i, v i ≠ 0)
    (he : ∀ i j, j < d i → v i ∉ P j) : LinearIndependent k v := by
  induction N with
  | zero => exact linearIndependent_empty_type
  | succ N ih =>
    cases N with
    | zero =>
      let _ : Unique (Fin 1) := ⟨⟨0⟩, fun a ↦ Fin.ext (by omega)⟩
      exact linearIndependent_unique_iff.mpr (hz default)
    | succ N =>
      apply linearIndependent_finSucc'.mpr
      constructor
      · exact ih (Fin.init v) (fun i ↦ d i.castSucc)
          (fun i j hij ↦ hd hij) (fun i ↦ hv i.castSucc)
          (fun i ↦ hz i.castSucc) (fun i j hij ↦ he i.castSucc j hij)
      · intro hm
        have hdpos : 0 < d (Fin.last (N + 1)) :=
          lt_of_le_of_lt (Nat.zero_le _) (hd (show (0 : Fin (N + 2)) < Fin.last (N + 1)
            from by change 0 < N + 1; omega))
        apply he (Fin.last (N + 1)) (d (Fin.last (N + 1)) - 1) (by omega)
        apply (Submodule.span_le.mpr ?_) hm
        rintro _ ⟨i, rfl⟩
        exact hP (show d i.castSucc ≤ d (Fin.last (N + 1)) - 1 from by
          have := hd (Fin.castSucc_lt_last i)
          omega) (hv i.castSucc)

/-- A full-dimensional family with distinct exact orders is a basis of its pole space. -/
def basisOfOrders (N D : ℕ) [NeZero N] (v : Fin N → V) (d : Fin N → ℕ)
    (hd : StrictMono d) (hv : ∀ i, v i ∈ P (d i)) (hz : ∀ i, v i ≠ 0)
    (he : ∀ i j, j < d i → v i ∉ P j) (hD : ∀ i, d i ≤ D)
    (hr : Module.finrank k (P D) = N) : Basis (Fin N) k (P D) :=
  basisOfLinearIndependentOfCardEqFinrank
    (LinearIndependent.of_comp (P D).subtype
      (linearIndependent_of_orders P hP N v d hd hv hz he))
    (by simpa only [Fintype.card_fin] using hr.symm)
    (b := fun i ↦ ⟨v i, hP (hD i) (hv i)⟩)

/-- The basis keeps the original ambient vectors, including their normalizations. -/
theorem basisOfOrders_apply (N D : ℕ) [NeZero N] (v : Fin N → V) (d : Fin N → ℕ)
    (hd : StrictMono d) (hv : ∀ i, v i ∈ P (d i)) (hz : ∀ i, v i ≠ 0)
    (he : ∀ i j, j < d i → v i ∉ P j) (hD : ∀ i, d i ≤ D)
    (hr : Module.finrank k (P D) = N) (i : Fin N) :
    (basisOfOrders P hP N D v d hd hv hz he hD hr i : V) = v i := by
  simp only [basisOfOrders, coe_basisOfLinearIndependentOfCardEqFinrank]

end FLT.Mazur.FilteredPoleBasis
