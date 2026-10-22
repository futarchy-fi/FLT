/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineLimitFlatCharts
public import FLT.Mazur.CoefficientOriginalHomDescent

/-!
# One coefficient refinement for tests on an original affine chart family

Independent Cartesian affine charts share one enlarged coefficient base.
The output keeps each chart's literal base change and trivializes its
specified original relation. This applies to any finite affine cover;
coverage and all existing marked whole-family data are unchanged.
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
  {T : Type*} [Finite T] {X Y : T → Scheme.{u}} [∀ t, IsAffine (Y t)]
  (r : ∀ t, X t ⟶ Spec (.of A)) [∀ t, Flat (r t)]
  (p : ∀ t, Y t ⟶ Spec (.of R)) (a : ∀ t, X t ⟶ Y t)
  (H : ∀ t, IsPullback (a t) (r t) (p t) (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
local notation "D" => fun t ↦ coefficientModelDiagram R (p t)
local notation "B" => coefficientSpectrumDiagram R

include H in
/-- Finite chart tests of the original flat family descend over one coefficient enlargement. -/
theorem exists_coefficient_affine_flat_chart_relations
    (K : T → Type*) [∀ t, Fintype (K t)] (i : (CoefficientStage R)ᵒᵖ)
    (f : ∀ t, K t → Γ((B).obj i, ⊤))
    (x : ∀ t, K t → Γ((D t).obj i, ⊤))
    (h : ∀ t, ∑ l, (r t).appTop
      (((coefficientSpectrumCone R).π.app i).appTop (f t l)) *
        (coefficientModelRecovery (H t) i).appTop (x t l) = 0) :
    ∃ (j : (CoefficientStage R)ᵒᵖ) (g : j ⟶ i), ∀ t,
      Trivial (pullback.snd (p t) ((coefficientSpectrumToInitial R).app j)).appTop.hom
        (fun l ↦ ((B).map g).appTop (f t l)) (fun l ↦ ((D t).map g).appTop (x t l)) := by
  let _ (j : (CoefficientStage R)ᵒᵖ) : IsAffine ((B).obj j) :=
    inferInstanceAs (IsAffine (Spec (.of j.unop.val)))
  let _ (t : T) (j : (CoefficientStage R)ᵒᵖ) : IsAffine ((D t).obj j) := by
    change IsAffine (pullback (p t) ((coefficientSpectrumToInitial R).app j))
    infer_instance
  let _ (t : T) : IsAffine (coefficientModelCone R (p t)).pt := by
    change IsAffine (pullback (p t) (Spec.map (CommRingCat.ofHom R.val.toRingHom)))
    infer_instance
  let _ (t : T) : IsAffine (X t) := .of_isIso (H t).isoPullback.hom
  let _ : IsAffine (coefficientSpectrumCone R).pt :=
    inferInstanceAs (IsAffine (Spec (.of A)))
  let c (t : T) : Cone (D t) :=
    (coefficientModelCone R (p t)).extend (H t).isoPullback.hom
  let _ (t : T) : IsAffine (c t).pt := inferInstanceAs (IsAffine (X t))
  have hc (t : T) : IsLimit (c t) :=
    IsLimit.extendIso (s := coefficientModelCone R (p t)) (H t).isoPullback.hom
      (coefficientModelIsLimit R (p t))
  let P (t : T) := schemeBaseChangeProjection (coefficientSpectrumToInitial R) (p t)
  have he (t : T) (j : (CoefficientStage R)ᵒᵖ) :
      (c t).π.app j = coefficientModelRecovery (H t) j :=
    coefficientModelRecovery_comparison (H t) j
  have hp (t : T) (j : (CoefficientStage R)ᵒᵖ) :
      (c t).π.app j ≫ (P t).app j = r t ≫ (coefficientSpectrumCone R).π.app j := by
    rw [he]
    exact (coefficientModelRecovery_isPullback (H t) j).w
  apply exists_affine_limit_flat_chart_relations D B c (coefficientSpectrumCone R)
    hc (coefficientSpectrumIsLimit R) P r hp K i f x
  intro t
  dsimp only [c, Cone.extend, NatTrans.comp_app, Functor.const_map_app]
  rw [coefficientModelRecovery_comparison]
  exact h t

end FLT.Mazur.Approximation
