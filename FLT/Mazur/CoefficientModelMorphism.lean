/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientModelHomDescent
public import FLT.Mazur.ProperCoverImmersionCriterion

/-!
# Morphisms between coefficient model systems

Base change of a map between fixed models commutes with every transition and
with recovery from the original ring. These identities let equations for an
inverse descend while keeping the original morphism.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

set_option backward.isDefEq.respectTransparency false

variable {A : Type u} [CommRing A] (S₀ : Subalgebra ℤ A)
  {Y Z : Scheme.{u}} (p : Y ⟶ Spec (.of S₀)) (q : Z ⟶ Spec (.of S₀))
  (f : Y ⟶ Z) (w : f ≫ q = p)

/-- The fixed map, base-changed at every coefficient stage. -/
def coefficientModelMorphism : coefficientModelDiagram S₀ p ⟶ coefficientModelDiagram S₀ q where
  app i := immersionBaseChange p q f w ((coefficientSpectrumToInitial S₀).app i)
  naturality _ _ _ := by
    apply pullback.hom_ext <;>
      simp [coefficientModelDiagram, schemeBaseChangeDiagram, Category.assoc]

/-- Model-map recovery commutes with the canonical limit projections. -/
@[reassoc]
lemma coefficientModelMorphism_recovery (i : (CoefficientStage S₀)ᵒᵖ) :
    (coefficientModelCone S₀ p).π.app i ≫ (coefficientModelMorphism S₀ p q f w).app i =
      immersionBaseChange p q f w (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)) ≫
        (coefficientModelCone S₀ q).π.app i := by
  apply pullback.hom_ext <;>
    simp [coefficientModelMorphism, coefficientModelCone, schemeBaseChangeCone, Category.assoc]

/-- The initial projection of a changed map is the original map after projection. -/
@[reassoc (attr := simp)]
lemma coefficientModelMorphism_toInitial (i : (CoefficientStage S₀)ᵒᵖ) :
    (coefficientModelMorphism S₀ p q f w).app i ≫ (coefficientModelToInitial S₀ q).app i =
      (coefficientModelToInitial S₀ p).app i ≫ f :=
  immersionBaseChange_fst p q f w ((coefficientSpectrumToInitial S₀).app i)

end FLT.Mazur.Approximation
