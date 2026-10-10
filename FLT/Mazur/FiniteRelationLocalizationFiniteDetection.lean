/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationLocalizationDetection

/-!
# Finite equality detection on localized relation models

A finite family of equalities holds on one common later principal-open model.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationLocalization

universe u v w

variable {R : Type u} [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) (r : P)

variable (R)

/-- Agreement at a later stage is equivalent to agreement in the full quotient. -/
theorem toQuotient_eq_iff (s : Finset I) (x y : Stage I r s) :
    toQuotient R I r s x = toQuotient R I r s y ↔
      ∃ (t : Finset I) (hst : s ≤ t), transition R I r hst x = transition R I r hst y := by
  refine ⟨exists_transition_eq R I r s x y, ?_⟩
  rintro ⟨t, hst, h⟩
  have hx := AlgHom.congr_fun (toQuotient_comp R I r hst) x
  have hy := AlgHom.congr_fun (toQuotient_comp R I r hst) y
  exact hx.symm.trans ((congrArg (toQuotient R I r t) h).trans hy)

/-- Finitely many quotient equalities hold simultaneously after one enlargement. -/
theorem exists_transition_eq_finite {ι : Type w} [Finite ι] (s : Finset I)
    (x y : ι → Stage I r s) (h : ∀ i, toQuotient R I r s (x i) = toQuotient R I r s (y i)) :
    ∃ (t : Finset I) (hst : s ≤ t),
      ∀ i, transition R I r hst (x i) = transition R I r hst (y i) := by
  classical
  let _ := Fintype.ofFinite ι
  choose t ht he using fun i ↦ exists_transition_eq R I r s (x i) (y i) (h i)
  let q := s ∪ Finset.univ.biUnion t
  have hsq : s ≤ q := Finset.subset_union_left
  have htq (i) : t i ≤ q := by
    intro z hz
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hz⟩)
  refine ⟨q, hsq, fun i ↦ ?_⟩
  have hc := transition_comp R I r (ht i) (htq i)
  exact (AlgHom.congr_fun hc (x i)).symm.trans
    ((congrArg (transition R I r (htq i)) (he i)).trans (AlgHom.congr_fun hc (y i)))

end FLT.Mazur.FiniteRelationLocalization
