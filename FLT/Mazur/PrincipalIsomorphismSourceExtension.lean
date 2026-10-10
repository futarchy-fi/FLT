/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypePrincipalIsomorphismDescent
public import FLT.Mazur.PrincipalCoordinateStages

/-!
# Extending the source of a principal-stage isomorphism

Any prescribed enlargement of the ambient source relations transports to a
finite target enlargement. The resulting map is again an isomorphism and its
square commutes. Different principal opens may therefore share new source
relations without abandoning previously constructed isomorphisms.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra.FiniteType R A] [Algebra.FiniteType R B]
  {a : A} {b : B}

/-- Enlarging the source of an actual coordinate isomorphism has an exact target lift. -/
theorem exists_principal_equiv_source_extension
    (e : Localization.Away a ≃ₐ[R] Localization.Away b)
    {s q : Finset (relationIdeal R A)} {t : Finset (relationIdeal R B)}
    (d : PrincipalStage R A a s ≃ₐ[R] PrincipalStage R B b t)
    (hd : (principalStageMap R B b t).comp d.toAlgHom =
      e.toAlgHom.comp (principalStageMap R A a s)) (hsq : s ≤ q) :
    ∃ (v : Finset (relationIdeal R B)) (htv : t ≤ v)
      (d' : PrincipalStage R A a q ≃ₐ[R] PrincipalStage R B b v),
      d'.toAlgHom.comp (principalTransition a hsq) =
        (principalTransition b htv).comp d.toAlgHom ∧
      (principalStageMap R B b v).comp d'.toAlgHom =
        e.toAlgHom.comp (principalStageMap R A a q) := by
  let g := (principalTransition a hsq).comp d.symm.toAlgHom
  have hg : Function.Surjective g :=
    (FiniteRelationLocalization.transition_surjective R (relationIdeal R A)
      (principalRepresentative R A a) hsq).comp d.symm.surjective
  have hfac : (principalStageMap R A a q).comp g =
      e.symm.toAlgHom.comp (principalStageMap R B b t) := by
    dsimp only [g]
    rw [← AlgHom.comp_assoc, principalStageMap_transition]
    apply AlgHom.ext
    intro x
    apply e.injective
    have h := AlgHom.congr_fun hd (d.symm x)
    simpa only [g, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.apply_symm_apply] using h.symm
  obtain ⟨v, htv, k, hk, hkfac⟩ :=
    exists_principal_lift_equiv b a e.symm.toAlgHom e.symm.injective t q g hg hfac
  refine ⟨v, htv, k.symm, ?_, ?_⟩
  · apply AlgHom.ext
    intro x
    apply k.injective
    have h := AlgHom.congr_fun hk (d x)
    simpa only [g, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.apply_symm_apply, AlgEquiv.symm_apply_apply] using h.symm
  · apply AlgHom.ext
    intro x
    apply e.symm.injective
    have h := AlgHom.congr_fun hkfac (k.symm x)
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.apply_symm_apply, AlgEquiv.symm_apply_apply] using h.symm

end FLT.Mazur.FiniteTypeRelationModel
