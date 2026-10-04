/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.MvPolynomial.OriginLocalizationMap

/-! # Descent of localized relations, including their denominators -/

@[expose] public noncomputable section

namespace MvPolynomial

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
  {n : ℕ}

/-- A finite list of fractions at the origin is defined over a finite coefficient field.
The finite field contains coefficients of both numerators and denominators. -/
theorem exists_finite_field_of_localized_list (rs : List (OriginLocalization Ω n)) :
    ∃ E : IntermediateField k Ω, FiniteDimensional k E ∧
      ∃ qs : List (OriginLocalization E n), qs.map (originLocalizationMap E Ω n) = rs := by
  classical
  let P := rationalPointIdeal (fun _ : Fin n ↦ (0 : Ω))
  choose num den hfrac using (IsLocalization.exists_mk'_eq P.primeCompl :
    ∀ x : OriginLocalization Ω n, ∃ a b, IsLocalization.mk' _ a b = x)
  let ps := rs.flatMap fun x ↦ [num x, (den x).val]
  obtain ⟨E, hE, fs, hfs⟩ := exists_finite_field_of_polynomial_list (k := k) ps
  have liftPoly (f : MvPolynomial (Fin n) Ω) (hf : f ∈ ps) :
      ∃ q : MvPolynomial (Fin n) E, map (algebraMap E Ω) q = f := by
    rw [← hfs] at hf
    obtain ⟨q, _, hq⟩ := List.mem_map.mp hf
    exact ⟨q, hq⟩
  have liftFrac (x : OriginLocalization Ω n) (hx : x ∈ rs) :
      ∃ y : OriginLocalization E n, originLocalizationMap E Ω n y = x := by
    obtain ⟨a, ha⟩ := liftPoly (num x) (List.mem_flatMap.mpr ⟨x, hx, by simp⟩)
    obtain ⟨b, hb⟩ := liftPoly (den x).val (List.mem_flatMap.mpr ⟨x, hx, by simp⟩)
    have hb' : b ∈ (rationalPointIdeal (fun _ : Fin n ↦ (0 : E))).primeCompl := by
      change b ∉ rationalPointIdeal _
      rw [originIdeal_comap_map E Ω n]
      change map (algebraMap E Ω) b ∉ P
      rw [hb]
      exact (den x).property
    refine ⟨IsLocalization.mk' _ a ⟨b, hb'⟩, ?_⟩
    rw [originLocalizationMap, Localization.localRingHom_mk']
    convert hfrac x using 1; simp [ha, hb]
  have liftList (xs : List (OriginLocalization Ω n))
      (hx : ∀ x ∈ xs, ∃ y, originLocalizationMap E Ω n y = x) :
      ∃ ys : List (OriginLocalization E n), ys.map (originLocalizationMap E Ω n) = xs := by
    induction xs with
    | nil => exact ⟨[], rfl⟩
    | cons x xs ih =>
      obtain ⟨y, hy⟩ := hx x (by simp)
      obtain ⟨ys, hys⟩ := ih (fun x hx' ↦ hx x (by simp [hx']))
      exact ⟨y :: ys, by simp [hy, hys]⟩
  exact ⟨E, hE, liftList rs liftFrac⟩

/-- Finite-field descent preserves the order, length and regularity of localized relations. -/
theorem exists_finite_field_of_localized_regular_list
    {rs : List (OriginLocalization Ω n)}
    (h : RingTheory.Sequence.IsRegular (OriginLocalization Ω n) rs) :
    ∃ E : IntermediateField k Ω, FiniteDimensional k E ∧
      ∃ qs : List (OriginLocalization E n), qs.map (originLocalizationMap E Ω n) = rs ∧
        qs.length = rs.length ∧ RingTheory.Sequence.IsRegular (OriginLocalization E n) qs := by
  obtain ⟨E, hE, qs, hqs⟩ := exists_finite_field_of_localized_list (k := k) rs
  refine ⟨E, hE, qs, hqs, ?_, (isRegular_originLocalizationMap_iff E Ω n qs).mp ?_⟩
  · rw [← hqs, List.length_map]
  · rwa [hqs]

end MvPolynomial
