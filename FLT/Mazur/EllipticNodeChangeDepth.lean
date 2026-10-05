/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeChangeResidue

/-!
# Translation depth between normalized split models

The coefficient equations imply r(b₂+6r) lies in the required ideal power.
The residual singularity calculation makes r small, so b₂+6r is a unit.
Thus both translations are deep; no iterative completeness argument is needed.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

/-- Changes between split models of the same depth have translations deeper than that depth. -/
theorem splitNodeDepth_change_translation_deep {R : Type*} [CommRing R] [IsLocalRing R]
    {W : WeierstrassCurve R} {π π' : R} {n : ℕ}
    (D : SplitNodeDepth W π n) (C : VariableChange R)
    (D' : SplitNodeDepth (C • W) π' n) :
    C.r ∈ maximalIdeal R ^ (n + 1) ∧ C.t ∈ maximalIdeal R ^ (n + 1) := by
  let I := maximalIdeal R ^ (n + 1)
  have hr := (splitNodeDepth_change_translation_mem D C D').1
  have h3 : W.a₃ + C.r * W.a₁ + 2 * C.t ∈ I := by
    have h := D'.a₃_mem
    rw [variableChange_a₃] at h
    exact (I.unit_mul_mem_iff_mem (C.u⁻¹.isUnit.pow 3)).mp h
  have h4 : W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ -
      (C.t + C.r * C.s) * W.a₁ + 3 * C.r ^ 2 - 2 * C.s * C.t ∈ I := by
    have h := D'.a₄_mem
    rw [variableChange_a₄] at h
    exact (I.unit_mul_mem_iff_mem (C.u⁻¹.isUnit.pow 4)).mp h
  have hlin3 : C.r * W.a₁ + 2 * C.t ∈ I := by
    convert I.sub_mem h3 D.a₃_mem using 1
    ring
  have hlin4 : 2 * C.r * W.a₂ - C.t * W.a₁ + 3 * C.r ^ 2 ∈ I := by
    convert I.sub_mem (I.add_mem h4 (I.mul_mem_left C.s h3)) D.a₄_mem using 1
    ring
  have hprod : C.r * (W.b₂ + 6 * C.r) ∈ I := by
    convert I.add_mem (I.mul_mem_left W.a₁ hlin3) (I.mul_mem_left 2 hlin4) using 1
    simp only [b₂]
    ring
  have hu : IsUnit (W.b₂ + 6 * C.r) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    have ha1 := (residue_ne_zero_iff_isUnit _).mpr D.a₁_unit
    simpa [b₂, (residue_eq_zero_iff _).mpr hr,
      (residue_eq_zero_iff _).mpr D.a₂_mem] using pow_ne_zero 2 ha1
  have hr' : C.r ∈ I := (I.mul_unit_mem_iff_mem hu).mp hprod
  refine ⟨hr', ?_⟩
  apply (I.mul_unit_mem_iff_mem D.a₁_unit).mp
  convert I.sub_mem (I.add_mem (I.mul_mem_right W.a₂ (I.mul_mem_left 2 hr'))
    (I.mul_mem_left 3 (I.pow_mem_of_mem hr' 2 (by decide)))) hlin4 using 1
  ring

end FLT.Mazur
