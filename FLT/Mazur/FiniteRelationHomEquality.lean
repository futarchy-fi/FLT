/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationDetection

/-!
# Finite-stage detection of equality between algebra maps

Maps from a finite-type algebra are equal when they agree on finitely many
generators. Equalities in the limiting quotient, including finitely many
compatibility equations, therefore hold at a common later relation stage.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P)

/-- Equality of maps from a finite-type algebra is detected at a later stage. -/
theorem exists_transition_hom_eq {A : Type w} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (s : Finset I) (f g : A →ₐ[R] Stage I s)
    (h : (toQuotient R I s).comp f = (toQuotient R I s).comp g) :
    ∃ (t : Finset I) (hst : s ≤ t),
      (transition R I hst).comp f = (transition R I hst).comp g := by
  obtain ⟨n, q, hq⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R A)
  obtain ⟨t, hst, ht⟩ := exists_transition_eq_finite R I s
    (fun i : Fin n ↦ f (q (MvPolynomial.X i)))
    (fun i : Fin n ↦ g (q (MvPolynomial.X i)))
    (fun i ↦ AlgHom.congr_fun h (q (MvPolynomial.X i)))
  refine ⟨t, hst, ?_⟩
  have he : ((transition R I hst).comp f).comp q =
      ((transition R I hst).comp g).comp q := by
    ext i
    exact ht i
  apply AlgHom.ext
  intro a
  obtain ⟨x, rfl⟩ := hq a
  exact AlgHom.congr_fun he x

/-- A finite family of map equalities can be imposed simultaneously. -/
theorem exists_transition_hom_eq_finite {ι : Type z} [Finite ι]
    (A : ι → Type w) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Algebra.FiniteType R (A i)] (s : Finset I)
    (f g : ∀ i, A i →ₐ[R] Stage I s)
    (h : ∀ i, (toQuotient R I s).comp (f i) = (toQuotient R I s).comp (g i)) :
    ∃ (t : Finset I) (hst : s ≤ t),
      ∀ i, (transition R I hst).comp (f i) = (transition R I hst).comp (g i) := by
  classical
  let _ := Fintype.ofFinite ι
  choose t ht he using fun i ↦ exists_transition_hom_eq I s (f i) (g i) (h i)
  let q := s ∪ Finset.univ.biUnion t
  have hsq : s ≤ q := Finset.subset_union_left
  have htq (i) : t i ≤ q := by
    intro x hx
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩)
  refine ⟨q, hsq, fun i ↦ ?_⟩
  have hc := transition_comp R I (ht i) (htq i)
  calc
    (transition R I hsq).comp (f i) =
        (transition R I (htq i)).comp ((transition R I (ht i)).comp (f i)) := by
      rw [← AlgHom.comp_assoc, hc]
    _ = (transition R I (htq i)).comp ((transition R I (ht i)).comp (g i)) := by
      rw [he i]
    _ = (transition R I hsq).comp (g i) := by rw [← AlgHom.comp_assoc, hc]

end FLT.Mazur.FiniteRelationModel
