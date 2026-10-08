/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypePrincipalMaps
public import FLT.Mazur.FiniteRelationLocalizationSurjectiveDescent

/-!
# Surjective coordinate lifts into principal-open models

Surjectivity of an original coordinate map is detected at a finite target
stage, keeping its source stage fixed. This supplies quotient presentations
for finite-stage identification arguments without asserting invertibility.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
  [Algebra.FiniteType R B] (b : B)


/-- A lift which is surjective on the original ring is surjective at a later stage. -/
theorem exists_principal_surjective_stage {T : Type w} [CommRing T] [Algebra R T]
    (s : Finset (relationIdeal R B)) (f : T →ₐ[R] PrincipalStage R B b s)
    (hf : Function.Surjective ((principalStageMap R B b s).comp f)) :
    ∃ (t : Finset (relationIdeal R B)) (hst : s ≤ t),
      Function.Surjective ((FiniteRelationLocalization.transition R (relationIdeal R B)
        (principalRepresentative R B b) hst).comp f) := by
  apply FiniteRelationLocalization.exists_surjective_stage
  intro x
  obtain ⟨y, hy⟩ := hf (principalQuotientEquiv R B b x)
  refine ⟨y, (principalQuotientEquiv R B b).injective ?_⟩
  exact hy

/-- Surjections from finitely presented algebras lift as finite-stage surjections. -/
theorem exists_principal_surjective_lift {T : Type w} [CommRing T] [Algebra R T]
    [Algebra.FinitePresentation R T] (f : T →ₐ[R] Localization.Away b)
    (hf : Function.Surjective f) (s : Finset (relationIdeal R B)) :
    ∃ t : Finset (relationIdeal R B), s ≤ t ∧
      ∃ g : T →ₐ[R] PrincipalStage R B b t,
        Function.Surjective g ∧ (principalStageMap R B b t).comp g = f := by
  obtain ⟨q, hsq, g, hg⟩ := exists_principal_hom_lift b f s
  obtain ⟨t, hqt, ht⟩ := exists_principal_surjective_stage b q g (hg.symm ▸ hf)
  refine ⟨t, hsq.trans hqt,
    (FiniteRelationLocalization.transition R (relationIdeal R B)
      (principalRepresentative R B b) hqt).comp g, ht, ?_⟩
  rw [← AlgHom.comp_assoc, principalStageMap_transition, hg]

variable {A : Type z} [CommRing A] [Algebra R A] [Algebra.FiniteType R A] (a : A)

/-- A surjective original coordinate map has a surjective lift from any fixed source stage. -/
theorem exists_principalStageMap_surjective_lift
    (f : Localization.Away a →ₐ[R] Localization.Away b) (hf : Function.Surjective f)
    (s : Finset (relationIdeal R A)) (t : Finset (relationIdeal R B)) :
    ∃ q : Finset (relationIdeal R B), t ≤ q ∧
      ∃ g : PrincipalStage R A a s →ₐ[R] PrincipalStage R B b q,
        Function.Surjective g ∧ (principalStageMap R B b q).comp g =
          f.comp (principalStageMap R A a s) :=
  exists_principal_surjective_lift b (f.comp (principalStageMap R A a s))
    (hf.comp (principalStageMap_surjective R A a s)) t

end FLT.Mazur.FiniteTypeRelationModel
