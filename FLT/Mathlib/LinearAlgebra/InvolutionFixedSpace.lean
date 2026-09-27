/-
Copyright (c) 2026 Kelvin Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelvin Santos
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Fixed spaces of two-dimensional involutions

An involution of determinant −1 in dimension two has one-dimensional eigenspaces
for both 1 and −1, provided the field has characteristic different from two.
-/

@[expose] public section

namespace Module.End

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- A two-dimensional involution of determinant −1 has a one-dimensional fixed space. -/
theorem finrank_eigenspace_one_of_involution
    (hV : Module.finrank k V = 2) (hchar : (2 : k) ≠ 0)
    (c : Module.End k V) (hc2 : c * c = 1) (hdet : LinearMap.det c = -1) :
    Module.finrank k (eigenspace c 1) = 1 := by
  have hone : (1 : k) ≠ -1 := by
    intro h
    apply hchar
    simpa [one_add_one_eq_two] using (eq_neg_iff_add_eq_zero.mp h)
  have hcne : c ≠ 1 := by
    intro h
    subst c
    exact hone (by simpa using hdet)
  have hcneg : c ≠ -1 := by
    intro h
    subst c
    apply hone
    rw [← neg_one_smul k (1 : Module.End k V), LinearMap.det_smul, hV] at hdet
    simpa using hdet
  have hbot : eigenspace c 1 ≠ ⊥ := by
    intro h
    apply hcneg
    ext x
    have hx : c x + x ∈ eigenspace c 1 := by
      rw [mem_eigenspace_iff]
      simp only [map_add, ← Module.End.mul_apply, hc2, one_apply, one_smul]
      exact add_comm _ _
    rw [h, Submodule.mem_bot] at hx
    simpa using (eq_neg_of_add_eq_zero_left hx)
  have htop : eigenspace c 1 ≠ ⊤ := by
    intro h
    apply hcne
    ext x
    have hx : x ∈ eigenspace c 1 := by rw [h]; trivial
    simpa [mem_eigenspace_iff] using hx
  have hlo := (Submodule.one_le_finrank_iff).mpr hbot
  have hhi := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr htop)
  rw [finrank_top, hV] at hhi
  exact Nat.le_antisymm (Nat.le_of_lt_succ hhi) hlo

/-- The −1 eigenspace of a two-dimensional involution of determinant −1 also has rank one. -/
theorem finrank_eigenspace_neg_one_of_involution
    (hV : Module.finrank k V = 2) (hchar : (2 : k) ≠ 0)
    (c : Module.End k V) (hc2 : c * c = 1) (hdet : LinearMap.det c = -1) :
    Module.finrank k (eigenspace c (-1)) = 1 := by
  have hnegdet : LinearMap.det (-c) = -1 := by
    rw [← neg_one_smul k c, LinearMap.det_smul, hV, hdet]
    simp
  have heq : eigenspace (-c) 1 = eigenspace c (-1) := by
    ext x
    simp [neg_eq_iff_eq_neg]
  rw [← heq]
  exact finrank_eigenspace_one_of_involution hV hchar (-c) (by simpa using hc2) hnegdet

end Module.End
