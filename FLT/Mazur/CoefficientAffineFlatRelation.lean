/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineLimitFlatRelation
public import FLT.Mazur.CoefficientOriginalHomDescent

/-!
# Finite flatness tests on fixed affine coefficient models

The given original affine family is retained through its Cartesian recovery.
Every specified finite family of relations becomes trivial on one literal
coefficient enlargement of the fixed model. No new geometric model is chosen.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped BigOperators
namespace FLT.Mazur.Approximation
open RingFlatRelation
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A : Type u} [CommRing A] (R : Subalgebra ℤ A) [Algebra.FiniteType ℤ R]
  {X Y : Scheme.{u}} [IsAffine Y] {r : X ⟶ Spec (.of A)} [Flat r]
  (p : Y ⟶ Spec (.of R)) {a : X ⟶ Y}
  (H : IsPullback a r p (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
local notation "D" => coefficientModelDiagram R p
local notation "B" => coefficientSpectrumDiagram R

include H in
/-- Finite relation tests of the original flat family descend on the unchanged affine model. -/
theorem exists_coefficient_affine_flat_relation_family
    {T : Type*} [Finite T] (K : T → Type*) [∀ t, Fintype (K t)]
    (i : (CoefficientStage R)ᵒᵖ)
    (f : ∀ t, K t → Γ((B).obj i, ⊤)) (x : ∀ t, K t → Γ((D).obj i, ⊤))
    (h : ∀ t, ∑ l, r.appTop (((coefficientSpectrumCone R).π.app i).appTop (f t l)) *
      (coefficientModelRecovery H i).appTop (x t l) = 0) :
    ∃ (j : (CoefficientStage R)ᵒᵖ) (g : j ⟶ i), ∀ t,
      Trivial (pullback.snd p ((coefficientSpectrumToInitial R).app j)).appTop.hom
        (fun l ↦ ((B).map g).appTop (f t l)) (fun l ↦ ((D).map g).appTop (x t l)) := by
  let _ (j : (CoefficientStage R)ᵒᵖ) : IsAffine ((B).obj j) :=
    inferInstanceAs (IsAffine (Spec (.of j.unop.val)))
  let _ (j : (CoefficientStage R)ᵒᵖ) : IsAffine ((D).obj j) := by
    change IsAffine (pullback p ((coefficientSpectrumToInitial R).app j))
    infer_instance
  let _ : IsAffine (coefficientModelCone R p).pt := by
    change IsAffine (pullback p (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
    infer_instance
  let _ : IsAffine X := .of_isIso H.isoPullback.hom
  let _ : IsAffine (coefficientSpectrumCone R).pt :=
    inferInstanceAs (IsAffine (Spec (.of A)))
  let c : Cone D := (coefficientModelCone R p).extend H.isoPullback.hom
  let _ : IsAffine c.pt := inferInstanceAs (IsAffine X)
  have hc : IsLimit c := IsLimit.extendIso (s := coefficientModelCone R p) H.isoPullback.hom
    (coefficientModelIsLimit R p)
  let P := schemeBaseChangeProjection (coefficientSpectrumToInitial R) p
  have he (j : (CoefficientStage R)ᵒᵖ) :
      c.π.app j = coefficientModelRecovery H j := coefficientModelRecovery_comparison H j
  have hp (j : (CoefficientStage R)ᵒᵖ) :
      c.π.app j ≫ P.app j = r ≫ (coefficientSpectrumCone R).π.app j := by
    rw [he]
    exact (coefficientModelRecovery_isPullback H j).w
  apply exists_affine_limit_flat_relation_family D B c (coefficientSpectrumCone R)
    hc (coefficientSpectrumIsLimit R) P r hp K i f x
  intro t
  dsimp only [c, Cone.extend, NatTrans.comp_app, Functor.const_map_app]
  rw [coefficientModelRecovery_comparison]
  exact h t

end FLT.Mazur.Approximation
