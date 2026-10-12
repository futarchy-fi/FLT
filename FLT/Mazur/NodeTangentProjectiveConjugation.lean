/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentNormalizationConjugation
public import FLT.Mazur.ProjectiveLineTranslationLinear
public import FLT.Mazur.ProjectiveCoefficientFunctor
public import FLT.Mazur.AffineSectionLineCoefficientMap

/-!
# Actual root conjugation on the complete normalization line

The affine operation z ↦ z+a extends to a projective involution over the
original ring. Its coefficient map is the actual tangent-root exchange.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur
open ProjectiveSpace ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "a" => WeierstrassCurve.a₁ (nodeTangentShear W)
local notation "σ" => RingEquiv.toRingHom (AlgEquiv.toRingEquiv (nodeTangentConjugation W))

/-- The complete normalization line retains its original tangent-root coefficient algebra. -/
def nodeTangentProjectiveConjugation : space S (ULift.{u} (Fin 2)) ⟶ space S (ULift.{u} (Fin 2)) :=
  (translationProjIso a).hom ≫ coefficientMap σ (ULift.{u} (Fin 2))

/-- The complete operation lies over the actual root exchange. -/
@[reassoc] theorem nodeTangentProjectiveConjugation_base :
    nodeTangentProjectiveConjugation W ≫ baseProjection S (ULift.{u} (Fin 2)) =
      baseProjection S (ULift.{u} (Fin 2)) ≫ Spec.map (CommRingCat.ofHom σ) := by
  rw [nodeTangentProjectiveConjugation, Category.assoc, coefficientMap_baseProjection,
    translationProjIso_base_assoc]

/-- The projective extension is an involution on the whole scheme, including infinity. -/
theorem nodeTangentProjectiveConjugation_involutive :
    nodeTangentProjectiveConjugation W ≫ nodeTangentProjectiveConjugation W = 𝟙 _ := by
  have hs : (σ).comp σ = RingHom.id S :=
    RingHom.ext (nodeTangentConjugationHom_involutive W)
  simp only [nodeTangentProjectiveConjugation, Category.assoc]
  rw [← Category.assoc (coefficientMap σ (ULift.{u} (Fin 2))), translation_coefficient,
    (show σ a = -a from nodeTangentShear_a₁_conjugate W), Category.assoc, coefficientMap_comp, hs,
    coefficientMap_id, Category.comp_id, translationProjIso_neg]

/-- The constructed extension is an actual isomorphism of complete schemes. -/
def nodeTangentProjectiveConjugationIso :
    space S (ULift.{u} (Fin 2)) ≅ space S (ULift.{u} (Fin 2)) where
  hom := nodeTangentProjectiveConjugation W
  inv := nodeTangentProjectiveConjugation W
  hom_inv_id := nodeTangentProjectiveConjugation_involutive W
  inv_hom_id := nodeTangentProjectiveConjugation_involutive W

/-- Its homogeneous coordinate formula holds over every affine test ring. -/
@[reassoc] theorem nodeTangentProjectiveConjugation_point
    {T : Type u} [CommRing T] (f : S →+* T) (x : (ULift.{u} (Fin 2)) → T)
    (i j : (ULift.{u} (Fin 2))) (b c : Tˣ) (hi : x i = b)
    (hj : (![x (ULift.up 0), x (ULift.up 1) + f a * x (ULift.up 0)] : Fin 2 → T)
      j.down = c) :
    unitChartPoint S (ULift.{u} (Fin 2)) f x i b hi ≫ nodeTangentProjectiveConjugation W =
      unitChartPoint S (ULift.{u} (Fin 2)) (f.comp σ)
        (fun k => ![x (ULift.up 0), x (ULift.up 1) + f a * x (ULift.up 0)] k.down)
        j c hj := by
  rw [nodeTangentProjectiveConjugation, ← Category.assoc]
  rw [show unitChartPoint S (ULift.{u} (Fin 2)) f x i b hi ≫ (translationProjIso a).hom = _ from
    unitChartPoint_linearIso_of_eval (translationLinear a).symm f x _
      (translation_evaluation a f x) i j b c hi hj]
  exact unitChartPoint_coefficientMap σ f _ j c hj

/-- The actual affine slope chart in the complete projective normalization. -/
def nodeTangentProjectiveChart : Spec (.of (Polynomial S)) ⟶ space S (ULift.{u} (Fin 2)) :=
  unitChartPoint S (ULift.{u} (Fin 2)) Polynomial.C
    (fun i => (![1, Polynomial.X] : Fin 2 → Polynomial S) i.down) (ULift.up 0) 1 rfl

/-- The projective extension restricts to the already constructed original affine involution. -/
@[reassoc] theorem nodeTangentProjectiveConjugation_chart :
    nodeTangentProjectiveChart W ≫ nodeTangentProjectiveConjugation W =
      Spec.map (CommRingCat.ofHom (nodeTangentNormalizationConjugation W).toRingHom) ≫
        nodeTangentProjectiveChart W := by
  rw [nodeTangentProjectiveChart, nodeTangentProjectiveConjugation_point W
    Polynomial.C _ (ULift.up 0) (ULift.up 0) 1 1 rfl rfl, unitChartPoint_map]
  have hc : Polynomial.C.comp σ =
      (nodeTangentNormalizationConjugation W).toRingHom.comp Polynomial.C := by
    apply RingHom.ext
    intro r
    exact (nodeTangentNormalizationConjugation_C W r).symm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    mul_one, hc, map_one]
  congr 1
  funext ⟨i⟩
  fin_cases i <;> simp

/-- Infinity is an actual section of the same complete normalization. -/
def nodeTangentProjectiveInfinity : Spec (.of S) ⟶ space S (ULift.{u} (Fin 2)) :=
  unitChartPoint S (ULift.{u} (Fin 2)) (.id S)
    (fun i => (![0, 1] : Fin 2 → S) i.down) (ULift.up 1) 1 rfl

/-- Infinity is retained with its actual semilinear coefficient map. -/
@[reassoc] theorem nodeTangentProjectiveConjugation_infinity :
    nodeTangentProjectiveInfinity W ≫ nodeTangentProjectiveConjugation W =
      Spec.map (CommRingCat.ofHom σ) ≫ nodeTangentProjectiveInfinity W := by
  rw [nodeTangentProjectiveInfinity, nodeTangentProjectiveConjugation_point W
    (.id S) _ (ULift.up 1) (ULift.up 1) 1 1 rfl (by simp), unitChartPoint_map]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    mul_zero, add_zero, RingHom.id_comp, RingHom.comp_id, map_one]
  congr 1
  funext ⟨i⟩
  fin_cases i <;> simp

end FLT.Mazur
