/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentProjectiveConjugation

/-!
# Specializing the actual root algebra and complete normalization operation

The tangent root, shear coefficient and conjugation commute with the
coefficient map of the original equation. In particular this applies to
its residue map, without replacing that equation by an unrelated nodal model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur
open ProjectiveSpace ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R T : Type u} [CommRing R] [CommRing T]
  (W : WeierstrassCurve R) (f : R →+* T)

/-- Tangent formation commutes with arbitrary original coefficient specialization. -/
theorem nodeTangentPolynomial_map_coefficients :
    nodeTangentPolynomial (W.map f) = (nodeTangentPolynomial W).map f := by
  simp [nodeTangentPolynomial]

/-- The actual integral root specializes to the root of the specialized original equation. -/
def nodeTangentCoefficientMap : AdjoinRoot (nodeTangentPolynomial W) →+*
    AdjoinRoot (nodeTangentPolynomial (W.map f)) :=
  AdjoinRoot.map f _ _ (by rw [nodeTangentPolynomial_map_coefficients])

@[simp] theorem nodeTangentCoefficientMap_root :
    nodeTangentCoefficientMap W f (AdjoinRoot.root (nodeTangentPolynomial W)) =
      AdjoinRoot.root (nodeTangentPolynomial (W.map f)) := AdjoinRoot.map_root _ _ _ _

/-- Original coefficients specialize through the original coefficient map. -/
theorem nodeTangentCoefficientMap_coeff (r : R) :
    nodeTangentCoefficientMap W f (algebraMap R _ r) = algebraMap T _ (f r) :=
  AdjoinRoot.map_of _ _ _ _ r

/-- Specialization retains the transverse coefficient of the actual root shear. -/
theorem nodeTangentCoefficientMap_shear :
    nodeTangentCoefficientMap W f (nodeTangentShear W).a₁ =
      (nodeTangentShear (W.map f)).a₁ := by
  rw [(nodeTangentShear_coefficients W).1, (nodeTangentShear_coefficients (W.map f)).1]
  simp only [map_add, map_mul, map_ofNat, nodeTangentCoefficientMap_coeff,
    nodeTangentCoefficientMap_root, WeierstrassCurve.map_a₁]

/-- The actual root involutions commute with coefficient specialization on every function. -/
theorem nodeTangentCoefficientMap_conjugation :
    (nodeTangentCoefficientMap W f).comp (nodeTangentConjugation W).toRingHom =
      (nodeTangentConjugation (W.map f)).toRingHom.comp (nodeTangentCoefficientMap W f) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro r
    change nodeTangentCoefficientMap W f (nodeTangentConjugation W (algebraMap R _ r)) =
      nodeTangentConjugation (W.map f)
        (nodeTangentCoefficientMap W f (algebraMap R _ r))
    rw [AlgEquiv.commutes, nodeTangentCoefficientMap_coeff, AlgEquiv.commutes]
  · change nodeTangentCoefficientMap W f
      (nodeTangentConjugationHom W (AdjoinRoot.root (nodeTangentPolynomial W))) =
        nodeTangentConjugationHom (W.map f)
          (nodeTangentCoefficientMap W f (AdjoinRoot.root (nodeTangentPolynomial W)))
    rw [nodeTangentConjugationHom_root, map_sub, map_neg,
      nodeTangentCoefficientMap_coeff, nodeTangentCoefficientMap_root,
      nodeTangentConjugationHom_root]
    rfl

/-- The full affine normalization operation specializes, with its actual coefficient map. -/
theorem nodeTangentCoefficientMap_normalization :
    (mapRingHom (nodeTangentCoefficientMap W f)).comp
        (nodeTangentNormalizationConjugation W).toRingHom =
      (nodeTangentNormalizationConjugation (W.map f)).toRingHom.comp
        (mapRingHom (nodeTangentCoefficientMap W f)) := by
  apply Polynomial.ringHom_ext
  · intro c
    change (nodeTangentNormalizationConjugation W (C c)).map _ =
      nodeTangentNormalizationConjugation (W.map f) ((C c).map _)
    rw [nodeTangentNormalizationConjugation_C, Polynomial.map_C,
      Polynomial.map_C, nodeTangentNormalizationConjugation_C]
    exact congrArg C (RingHom.congr_fun (nodeTangentCoefficientMap_conjugation W f) c)
  · change (nodeTangentNormalizationConjugation W X).map _ =
      nodeTangentNormalizationConjugation (W.map f) (X.map _)
    rw [nodeTangentNormalizationConjugation_X, Polynomial.map_add, Polynomial.map_X,
      Polynomial.map_C, nodeTangentCoefficientMap_shear, nodeTangentNormalizationConjugation_X]

/-- The complete projective operation specializes along the actual tangent-algebra map. -/
@[reassoc] theorem nodeTangentCoefficientMap_projective :
    coefficientMap (nodeTangentCoefficientMap W f) (ULift.{u} (Fin 2)) ≫
        nodeTangentProjectiveConjugation W =
      nodeTangentProjectiveConjugation (W.map f) ≫
        coefficientMap (nodeTangentCoefficientMap W f) (ULift.{u} (Fin 2)) := by
  simp only [nodeTangentProjectiveConjugation]
  rw [← Category.assoc, translation_coefficient, nodeTangentCoefficientMap_shear]
  simp only [Category.assoc, coefficientMap_comp]
  rw [nodeTangentCoefficientMap_conjugation]

end FLT.Mazur
