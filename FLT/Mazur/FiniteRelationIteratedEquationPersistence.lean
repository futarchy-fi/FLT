/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationIteratedFiniteMaps

/-!
# Persistence of full-ring equations on iterated principal opens

Once two maps agree at a relation stage, their equality survives every
later transition of the principal subopen.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteRelationIterated

universe u v w

variable (R : Type u) [CommRing R] {P : Type v} [CommRing P] [Algebra R P]
  (I : Ideal P) (r : P) (s : Finset I) (d : FiniteRelationLocalization.Stage I r s)

/-- Transport a full-ring equation along any further relation refinement. -/
theorem hom_eq_of_le {A : Type w} [CommRing A] [Algebra R A]
    {t q k : Set.Ici s} (htq : t ≤ q) (hqk : q ≤ k)
    (f g : A →ₐ[R] Stage R I r s d t)
    (h : (transition R I r s d htq).comp f = (transition R I r s d htq).comp g) :
    (transition R I r s d (htq.trans hqk)).comp f =
      (transition R I r s d (htq.trans hqk)).comp g := by
  rw [← transition_comp R I r s d htq hqk, AlgHom.comp_assoc, h, ← AlgHom.comp_assoc]

end FLT.Mazur.FiniteRelationIterated
