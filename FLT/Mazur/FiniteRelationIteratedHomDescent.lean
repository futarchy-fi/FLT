/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationIteratedDetection

/-!
# Finite presentation descent into iterated localizations

Lift polynomial generators and kill their finite relations. Equalities of maps
from finite-type sources are imposed on their generators at a common later stage.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationIterated

universe u v w z

variable {R : Type u} [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) (r : P) (s : Finset I) (d : FiniteRelationLocalization.Stage I r s)

/-- A finitely generated ideal killed in the original double open dies at a finite stage. -/
theorem exists_transition_kills_ideal {A : Type w} [CommRing A] [Algebra R A]
    (J : Ideal A) (hJ : J.FG) (t : Set.Ici s) (g : A →ₐ[R] Stage R I r s d t)
    (hg : J ≤ RingHom.ker ((toQuotient R I r s d t).comp g).toRingHom) :
    ∃ (q : Set.Ici s) (htq : t ≤ q),
      J ≤ RingHom.ker ((transition R I r s d htq).comp g).toRingHom := by
  classical
  obtain ⟨a, ha⟩ := hJ
  have hk (i : a) : toQuotient R I r s d t (g i.val) =
      toQuotient R I r s d t 0 := by
    rw [map_zero]
    exact hg (ha ▸ Submodule.subset_span i.property)
  obtain ⟨q, htq, hq⟩ := exists_transition_eq_finite R I r s d t
    (fun i : a ↦ g i.val) (fun _ ↦ 0) hk
  refine ⟨q, htq, ?_⟩
  rw [← ha]
  apply Submodule.span_le.mpr
  intro x hx
  exact (hq ⟨x, hx⟩).trans (map_zero _)

/-- Every map from a finitely presented algebra descends to an actual finite double open. -/
theorem exists_hom_lift {A : Type w} [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] (t : Set.Ici s) (f : A →ₐ[R] Quotient R I r s d) :
    ∃ q : Set.Ici s, t ≤ q ∧ ∃ g : A →ₐ[R] Stage R I r s d q,
      (toQuotient R I r s d q).comp g = f := by
  obtain ⟨n, p, hp, hker⟩ := Algebra.FinitePresentation.out (R := R) (A := A)
  obtain ⟨g, hg⟩ := FiniteRelationModel.exists_polynomial_lift (toQuotient R I r s d t)
    (toQuotient_surjective R I r s d t) (f.comp p)
  have hk : RingHom.ker p.toRingHom ≤
      RingHom.ker ((toQuotient R I r s d t).comp g).toRingHom := by
    rw [hg]
    intro x hx
    change f (p x) = 0
    change p x = 0 at hx
    rw [hx, map_zero]
  obtain ⟨q, htq, hq⟩ := exists_transition_kills_ideal I r s d _ hker t g hk
  refine ⟨q, htq, p.liftOfSurjective hp ((transition R I r s d htq).comp g) hq, ?_⟩
  apply AlgHom.ext
  intro a
  obtain ⟨x, rfl⟩ := hp a
  rw [AlgHom.comp_apply, AlgHom.liftOfSurjective_apply]
  change toQuotient R I r s d q (transition R I r s d htq (g x)) = f (p x)
  rw [← AlgHom.comp_apply, toQuotient_comp]
  exact AlgHom.congr_fun hg x

/-- Equality of maps from a finite-type algebra is detected on a later double open. -/
theorem exists_transition_hom_eq {A : Type w} [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (t : Set.Ici s) (f g : A →ₐ[R] Stage R I r s d t)
    (h : (toQuotient R I r s d t).comp f = (toQuotient R I r s d t).comp g) :
    ∃ (q : Set.Ici s) (htq : t ≤ q),
      (transition R I r s d htq).comp f = (transition R I r s d htq).comp g := by
  obtain ⟨n, p, hp⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R A)
  obtain ⟨q, htq, hq⟩ := exists_transition_eq_finite R I r s d t
    (fun i : Fin n ↦ f (p (MvPolynomial.X i)))
    (fun i : Fin n ↦ g (p (MvPolynomial.X i)))
    (fun i ↦ AlgHom.congr_fun h (p (MvPolynomial.X i)))
  refine ⟨q, htq, ?_⟩
  have he : ((transition R I r s d htq).comp f).comp p =
      ((transition R I r s d htq).comp g).comp p := by
    ext i
    exact hq i
  exact (AlgHom.cancel_right hp).mp he

end FLT.Mazur.FiniteRelationIterated
