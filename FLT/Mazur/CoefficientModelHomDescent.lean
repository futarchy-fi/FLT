/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientModelFiniteness

/-!
# Morphisms and their equations at finite coefficient stages

Maps from the recovered model to a finitely presented target descend to a
coefficient stage. Equalities of maps to a finite-type target hold after a
further enlargement. Both statements retain the original maps to the base.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {A : Type u} [CommRing A] (S₀ : Subalgebra ℤ A)
  {Z Y : Scheme.{u}} (q : Z ⟶ Spec (.of S₀))

/-- Projection from each enlarged scheme to the initial model. -/
def coefficientModelToInitial :
    coefficientModelDiagram S₀ q ⟶ (Functor.const _).obj Z where
  app i := pullback.fst q ((coefficientSpectrumToInitial S₀).app i)
  naturality _ _ _ := by simp [coefficientModelDiagram, schemeBaseChangeDiagram]

/-- The recovery projections retain the initial model map. -/
@[reassoc (attr := simp)]
lemma coefficientModelCone_toInitial (i : (CoefficientStage S₀)ᵒᵖ) :
    (coefficientModelCone S₀ q).π.app i ≫ (coefficientModelToInitial S₀ q).app i =
      pullback.fst q (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)) := by
  simp [coefficientModelCone, schemeBaseChangeCone, coefficientModelToInitial]

variable [Algebra.FiniteType ℤ S₀] [QuasiCompact q] [LocallyOfFiniteType q]

/-- A map from the recovered family to a finitely presented target descends. -/
theorem exists_coefficient_model_hom (p : Y ⟶ Spec (.of S₀))
    [LocallyOfFinitePresentation p] (a : (coefficientModelCone S₀ q).pt ⟶ Y)
    (ha : a ≫ p = pullback.fst q
      (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)) ≫ q) :
    ∃ (i : (CoefficientStage S₀)ᵒᵖ) (b : (coefficientModelDiagram S₀ q).obj i ⟶ Y),
      (coefficientModelCone S₀ q).π.app i ≫ b = a ∧
      b ≫ p = (coefficientModelToInitial S₀ q).app i ≫ q := by
  have (i : (CoefficientStage S₀)ᵒᵖ) :
      IsNoetherian ((coefficientModelDiagram S₀ q).obj i) := coefficientModel_isNoetherian q i
  exact Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (coefficientModelDiagram S₀ q)
    (coefficientModelToInitial S₀ q ≫ (Functor.const _).map q) p
    (coefficientModelCone S₀ q) (coefficientModelIsLimit S₀ q) a (by
      ext i
      simpa only [NatTrans.comp_app, Functor.const_map_app, ← Category.assoc,
        coefficientModelCone_toInitial] using ha.symm)

/-- Equality after recovery is equality at a finite enlargement of the same model. -/
theorem exists_coefficient_model_hom_eq (p : Y ⟶ Spec (.of S₀))
    [LocallyOfFiniteType p] {i : (CoefficientStage S₀)ᵒᵖ}
    (a b : (coefficientModelDiagram S₀ q).obj i ⟶ Y)
    (ha : a ≫ p = (coefficientModelToInitial S₀ q).app i ≫ q)
    (hb : b ≫ p = (coefficientModelToInitial S₀ q).app i ≫ q)
    (hab : (coefficientModelCone S₀ q).π.app i ≫ a =
      (coefficientModelCone S₀ q).π.app i ≫ b) :
    ∃ (j : (CoefficientStage S₀)ᵒᵖ) (f : j ⟶ i),
      (coefficientModelDiagram S₀ q).map f ≫ a =
        (coefficientModelDiagram S₀ q).map f ≫ b := by
  have (j : (CoefficientStage S₀)ᵒᵖ) :
      IsNoetherian ((coefficientModelDiagram S₀ q).obj j) := coefficientModel_isNoetherian q j
  exact Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (coefficientModelDiagram S₀ q)
    (coefficientModelToInitial S₀ q ≫ (Functor.const _).map q) p
    (coefficientModelCone S₀ q) (coefficientModelIsLimit S₀ q)
    a b ha.symm hb.symm hab

end FLT.Mazur.Approximation
