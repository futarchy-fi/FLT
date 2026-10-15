/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineEndpointReversal

/-!
# Propagating constant maps along an actual projective cycle

The endpoint equations identify the values of every contracted component
with the zero endpoint of the retained component. No reduced-point argument
is used: all equalities are equalities of scheme morphisms.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.ProjectiveCycleConstantPropagation
universe u
variable (K : Type u) [Field K] {Y : Scheme.{u}}

/-- Reparameterization over the base preserves constancy at the zero section. -/
theorem reparam_constant (f : ProjectiveLine.scheme K ⟶ Y)
    (hf : f = ProjectiveLine.toBase K ≫ ProjectiveLine.zero K ≫ f)
    (r : ProjectiveLine.scheme K ⟶ ProjectiveLine.scheme K)
    (hr : r ≫ ProjectiveLine.toBase K = ProjectiveLine.toBase K) :
    r ≫ f = ProjectiveLine.toBase K ≫ ProjectiveLine.zero K ≫ r ≫ f := by
  calc
    r ≫ f = ProjectiveLine.toBase K ≫ ProjectiveLine.zero K ≫ f := by
      conv_lhs => rw [hf]
      rw [← Category.assoc, hr]
    _ = ProjectiveLine.toBase K ≫ ProjectiveLine.zero K ≫ r ≫ f := by
      conv_rhs => rw [hf]
      simp only [← Category.assoc, hr, ProjectiveLine.zero_toBase, Category.id_comp]

variable {m : ℕ} (c : Fin (m + 1) → (ProjectiveLine.scheme K ⟶ Y))
  (hc : ∀ i, i ≠ 0 → c i = ProjectiveLine.toBase K ≫ ProjectiveLine.zero K ≫ c i)
  (he : ∀ i, ProjectiveLine.zero K ≫ c i =
    ProjectiveLine.infinity K ≫ c (PolygonPinching.next (by omega) i))

include hc he in
/-- Every zero endpoint has the same image as the retained component's zero endpoint. -/
theorem zero_eq (i : Fin (m + 1)) :
    ProjectiveLine.zero K ≫ c i = ProjectiveLine.zero K ≫ c 0 := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    have hn : PolygonPinching.next (by omega) i.castSucc = i.succ := by
      apply Fin.ext
      change (i.val + 1) % (m + 1) = i.val + 1
      exact Nat.mod_eq_of_lt (by omega)
    have h := he i.castSucc
    rw [hn, hc i.succ (by simp), ProjectiveLine.infinity_toBase_assoc] at h
    exact h.symm.trans ih

include hc he in
/-- Each omitted whole component maps to the single common endpoint value. -/
theorem component_eq (i : Fin (m + 1)) (hi : i ≠ 0) :
    c i = ProjectiveLine.toBase K ≫ ProjectiveLine.zero K ≫ c 0 := by
  rw [hc i hi, zero_eq K c hc he i]

end FLT.Mazur.ProjectiveCycleConstantPropagation
