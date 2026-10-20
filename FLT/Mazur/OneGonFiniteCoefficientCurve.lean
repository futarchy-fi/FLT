/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonFiniteCoefficientRecovery
public import FLT.Mazur.OneGonSmoothingCoefficientChange
public import FLT.Mazur.WeierstrassCoefficientChartTransport
public import FLT.Mazur.CharacterCoefficientCartesian

/-!
# Recovering the whole original cubic embedding

The descended chart coordinates define a morphism into the whole cubic.
Its coefficient square recovers the original morphism and is Cartesian,
retaining the actual finite character source and both projections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.OneGonFiniteCoefficientCoordinates

open WeierstrassIntegralChart OneGonSmoothing CharacterSchemeBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R G : Type} [CommRing R] [AddCommMonoid G]
  (t : R) (j : Fin 3) (φ : Coordinate (equation t) j →ₐ[R] AddMonoidAlgebra R G)

/-- The full cubic morphism specified by the original chart coordinates. -/
def coordinateCurveMap : (model R G).left ⟶ integralCurve (equation t) :=
  Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ integralCurveChart (equation t) j

/-- The original coordinate morphism retains its entire coefficient base. -/
@[reassoc] theorem coordinateCurveMap_structure :
    coordinateCurveMap t j φ ≫ integralCurveStructure (equation t) = (model R G).hom := by
  rw [coordinateCurveMap, Category.assoc, integralCurveChart_structure]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact φ.commutes a

variable (s : Set R)

/-- The descended morphism into the entire model cubic. -/
def modelCurveMap : (model (modelRing t j φ s) G).left ⟶
    integralCurve (equation (modelParameter t j φ s)) :=
  coordinateCurveMap (modelParameter t j φ s) j (modelCoordinates t j φ s)

/-- The actual whole-cubic coefficient projection. -/
def modelCurveProjection : integralCurve (equation t) ⟶
    integralCurve (equation (modelParameter t j φ s)) :=
  coefficientMorphism (S := R) (modelParameter t j φ s)

/-- The full model curve map is over its original finite coefficient ring. -/
@[reassoc] theorem modelCurveMap_structure :
    modelCurveMap t j φ s ≫ integralCurveStructure (equation (modelParameter t j φ s)) =
      (model (modelRing t j φ s) G).hom :=
  coordinateCurveMap_structure _ _ _

/-- Recovery commutes on the whole original cubic, including the boundary. -/
theorem modelCurveMap_recovery :
    Spec.map (CommRingCat.ofHom (modelInclusion t j φ s)) ≫ modelCurveMap t j φ s =
      coordinateCurveMap t j φ ≫ modelCurveProjection t j φ s := by
  have h := chartCoefficientRingMapTo_inclusion (modelRing t j φ s).val.toRingHom
    (equation (modelParameter t j φ s)) j (equation t) (equation_map _ _)
  change Spec.map (CommRingCat.ofHom (modelChartMap t j φ s)) ≫
    integralCurveChart (equation (modelParameter t j φ s)) j =
      integralCurveChart (equation t) j ≫ modelCurveProjection t j φ s at h
  change Spec.map _ ≫ Spec.map _ ≫ _ = (Spec.map _ ≫ _) ≫ _
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    modelCoordinates_recovery, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, h]
  exact (Category.assoc _ _ _).symm

/-- The recovered embedding is the Cartesian pullback of the actual model curve map. -/
theorem modelCurveMap_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (modelInclusion t j φ s)))
      (coordinateCurveMap t j φ) (modelCurveMap t j φ s) (modelCurveProjection t j φ s) := by
  have h : IsPullback (Spec.map (CommRingCat.ofHom (modelInclusion t j φ s)))
      (coordinateCurveMap t j φ ≫ integralCurveStructure (equation t))
      (modelCurveMap t j φ s ≫
        integralCurveStructure (equation (modelParameter t j φ s)))
      (baseMap (modelRing t j φ s) R) := by
    rw [coordinateCurveMap_structure, modelCurveMap_structure]
    exact coefficientMap_isPullback (modelRing t j φ s) R G
  exact h.of_bot (modelCurveMap_recovery t j φ s)
    (coefficient_isPullback (modelParameter t j φ s))

end FLT.Mazur.OneGonFiniteCoefficientCoordinates
