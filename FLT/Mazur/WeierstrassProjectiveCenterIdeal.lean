/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassProjectiveSingularCenter
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Scheme-theoretic center containment for the polynomial addition charts

The original homogeneous calculation descends through every ideal quotient.
In particular it preserves the actual modification center on mixed input charts;
output-X and output-Y domains have empty intersection with that center.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- Every polynomial presentation preserves center ideals under arbitrary specialization. -/
theorem projectiveSpecialization_output_mem_center (j k t : Fin 3)
    (f : AdditionOutputOpen W j k t →ₐ[R] S) (I : Ideal S)
    (h3 : algebraMap R S W.a₃ ∈ I) (h4 : algebraMap R S W.a₄ ∈ I)
    (h6 : algebraMap R S W.a₆ ∈ I)
    (hx : f (additionOutputRestriction W j k t
      (chartProductRight W j k (coord W k 0))) ∈ I)
    (hy : f (additionOutputRestriction W j k t
      (chartProductRight W j k (coord W k 1))) ∈ I) :
    f (projectiveAdditionChart W j k t (coord W t 0)) ∈ I ∧
      f (projectiveAdditionChart W j k t (coord W t 1)) ∈ I := by
  let q : S →ₐ[R] S ⧸ I := Ideal.Quotient.mkₐ R I
  have h := projectiveSpecialization_singular_origin W j k t (q.comp f)
    (by
      rw [IsScalarTower.algebraMap_apply R S (S ⧸ I)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h3)
    (by
      rw [IsScalarTower.algebraMap_apply R S (S ⧸ I)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h4)
    (by
      rw [IsScalarTower.algebraMap_apply R S (S ⧸ I)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h6)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hx) (Ideal.Quotient.eq_zero_iff_mem.mpr hy)
  exact ⟨Ideal.Quotient.eq_zero_iff_mem.mp h.1, Ideal.Quotient.eq_zero_iff_mem.mp h.2⟩

/-- The polynomial action sends both coordinates into the actual scale center. -/
theorem projectiveSpecialization_modificationCenter (j k t : Fin 3)
    (f : AdditionOutputOpen W j k t →ₐ[R] S) (s b3 b4 b6 : R)
    (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s * b6) :
    let I : Ideal S := Ideal.span
      {algebraMap R S s,
        f (additionOutputRestriction W j k t (chartProductRight W j k (coord W k 0))),
        f (additionOutputRestriction W j k t (chartProductRight W j k (coord W k 1)))}
    f (projectiveAdditionChart W j k t (coord W t 0)) ∈ I ∧
      f (projectiveAdditionChart W j k t (coord W t 1)) ∈ I := by
  dsimp only
  apply projectiveSpecialization_output_mem_center W j k t f
  · rw [h3, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · rw [h4, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · rw [h6, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · exact Ideal.subset_span (by simp)
  · exact Ideal.subset_span (by simp)

/-- Output-X and output-Y polynomial domains miss every such center scheme. -/
theorem projectiveSpecialization_center_eq_top (j k t : Fin 3) (ht : t = 0 ∨ t = 1)
    (f : AdditionOutputOpen W j k t →ₐ[R] S) (I : Ideal S)
    (h3 : algebraMap R S W.a₃ ∈ I) (h4 : algebraMap R S W.a₄ ∈ I)
    (h6 : algebraMap R S W.a₆ ∈ I)
    (hx : f (additionOutputRestriction W j k t
      (chartProductRight W j k (coord W k 0))) ∈ I)
    (hy : f (additionOutputRestriction W j k t
      (chartProductRight W j k (coord W k 1))) ∈ I) : I = ⊤ := by
  have h := projectiveSpecialization_output_mem_center W j k t f I h3 h4 h6 hx hy
  apply (Ideal.eq_top_iff_one I).mpr
  rcases ht with rfl | rfl
  · simpa only [coord_self, map_one] using h.1
  · simpa only [coord_self, map_one] using h.2

end FLT.Mazur.WeierstrassIntegralChart
