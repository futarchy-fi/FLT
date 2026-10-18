/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassComparisonCoefficientHom
public import FLT.Mazur.WeierstrassComparisonPresentationBaseChange

/-!
# The comparison pullback retains the original coefficient morphism

The second projection of the tensor-based scheme comparison is the spectrum
of the actual comparison algebra morphism preserving every change coordinate.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry WeierstrassCurve
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassChangeParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
  (W V : WeierstrassCurve R)
local notation "W'" => W.map (algebraMap R A)
local notation "V'" => V.map (algebraMap R A)
local notation "Q'" => EquationRing W' V'

/-- The coefficient classification of the universal parameter is the original coefficient map. -/
theorem coefficientParameterEquiv_id :
    (coefficientParameterEquiv W V (AlgHom.id A Q')).toRingHom =
      comparisonPresentationHom W V W' V' (algebraMap R A) rfl rfl := by
  apply comparisonPresentationHom_ext W V W' V' (algebraMap R A)
  · exact (coefficientParameterEquiv W V (AlgHom.id A Q')).comp_algebraMap
  · exact comparisonPresentationHom_base W V W' V' _ rfl rfl
  · rw [coefficientParameterEquiv_change, comparisonPresentationHom_change]
    exact VariableChange.map_id _

/-- The actual tensor morphism restricts to the original comparison coefficient morphism. -/
theorem coefficientTensorForward_includeRight :
    (coefficientTensorForward (A := A) W V).toRingHom.comp
      (Algebra.TensorProduct.includeRight :
        EquationRing W V →ₐ[R] A ⊗[R] EquationRing W V).toRingHom =
      comparisonPresentationHom W V W' V' (algebraMap R A) rfl rfl := by
  apply RingHom.ext
  intro x
  change (tensorParameterEquiv W V Q' (AlgHom.id A Q')) (1 ⊗ₜ[R] x) = _
  simp only [tensorParameterEquiv, Equiv.trans_apply, AlgHom.liftEquiv_tmul, one_smul]
  exact DFunLike.congr_fun (coefficientParameterEquiv_id (A := A) W V) x

/-- The second geometric projection is the original full comparison coefficient map. -/
@[reassoc] theorem comparisonCoefficientBaseChangeIso_snd :
    (comparisonCoefficientBaseChangeIso (A := A) W V).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (comparisonPresentationHom W V W' V' (algebraMap R A) rfl rfl)) := by
  change (Scheme.Spec.mapIso
    (coefficientTensorEquiv (A := A) W V).toRingEquiv.toCommRingCatIso.op).hom ≫
      (pullbackSpecIso R A (EquationRing W V)).inv ≫ pullback.snd _ _ = _
  rw [pullbackSpecIso_inv_snd]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (coefficientTensorForward_includeRight (A := A) W V)

variable (W₁ V₁ : WeierstrassCurve A) (f : R →+* A)
  (hW : W₁ = W.map f) (hV : V₁ = V.map f)

omit [Algebra R A] in
/-- Named-equation transport retains the same original comparison coefficient projection. -/
@[reassoc] theorem comparisonPresentationBaseChangeIso_snd :
    (comparisonPresentationBaseChangeIso W V W₁ V₁ f hW hV).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (comparisonPresentationHom W V W₁ V₁ f hW hV)) := by
  subst W₁
  subst V₁
  let _ : Algebra R A := f.toAlgebra
  exact comparisonCoefficientBaseChangeIso_snd (A := A) W V

end FLT.Mazur.WeierstrassChangeParameter
