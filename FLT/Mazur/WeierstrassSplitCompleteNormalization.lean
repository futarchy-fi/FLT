/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineValuationExtension
public import FLT.Mazur.WeierstrassIntegralProper

/-!
# Complete normalization of the split nodal cubic

The affine formula x=z(z+a₁), y=xz extends uniquely across infinity by
properness. It will compare both the actual incidence component and the
root-sheared normalization without assuming a complete comparison map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur
open Polynomial ProjectiveLine WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (W : WeierstrassCurve K)
  (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0)

include h₂ h₃ h₄ h₆ in
/-- The split normalization satisfies the original homogeneous cubic equation. -/
theorem splitNormalization_equation :
    (W.map (algebraMap K K[X])).toProjective.Equation
      ![X * (X + C W.a₁), X * (X + C W.a₁) * X, 1] := by
  rw [WeierstrassCurve.Projective.equation_iff]
  change (X * (X + C W.a₁) * X) ^ 2 * 1 +
    C W.a₁ * (X * (X + C W.a₁)) * (X * (X + C W.a₁) * X) * 1 +
    C W.a₃ * (X * (X + C W.a₁) * X) * 1 ^ 2 -
    ((X * (X + C W.a₁)) ^ 3 + C W.a₂ * (X * (X + C W.a₁)) ^ 2 * 1 +
      C W.a₄ * (X * (X + C W.a₁)) * 1 ^ 2 + C W.a₆ * 1 ^ 3) = 0
  rw [h₂, h₃, h₄, h₆, map_zero]
  ring

/-- The normalization algebra map keeps the split cubic's original coordinates. -/
def splitNormalizationChart : Coordinate W 2 →ₐ[K] K[X] :=
  evaluation W 2 ![X * (X + C W.a₁), X * (X + C W.a₁) * X, 1]
    (splitNormalization_equation W h₂ h₃ h₄ h₆) rfl

/-- The actual three homogeneous affine coordinates of the normalization. -/
@[simp] theorem splitNormalizationChart_coord (i : Fin 3) :
    splitNormalizationChart W h₂ h₃ h₄ h₆ (coord W 2 i) =
      ![X * (X + C W.a₁), X * (X + C W.a₁) * X, 1] i :=
  evaluation_coord _ _ _ _ _ i

/-- The full affine normalization as a morphism to the original proper cubic. -/
def splitAffineToCubic : chart K ⟶ integralCurve W :=
  Spec.map (CommRingCat.ofHom (splitNormalizationChart W h₂ h₃ h₄ h₆).toRingHom) ≫
    integralCurveChart W 2

/-- The full affine normalization preserves the coefficient projection. -/
@[reassoc] theorem splitAffineToCubic_base :
    splitAffineToCubic W h₂ h₃ h₄ h₆ ≫ integralCurveStructure W =
      left K ≫ toBase K := by
  rw [splitAffineToCubic, Category.assoc, integralCurveChart_structure,
    chartStructure, specAlgHom_structure, left_toBase]
  rfl

/-- Properness constructs the whole split normalization, including infinity. -/
theorem existsUnique_splitCompleteNormalization :
    ∃! f : scheme K ⟶ integralCurve W,
      f ≫ integralCurveStructure W = toBase K ∧
        left K ≫ f = splitAffineToCubic W h₂ h₃ h₄ h₆ :=
  existsUnique_left_extension K (toBase K) (integralCurveStructure W)
    (splitAffineToCubic W h₂ h₃ h₄ h₆) (splitAffineToCubic_base W h₂ h₃ h₄ h₆)

/-- The constructed complete split normalization morphism. -/
def splitCompleteNormalization : scheme K ⟶ integralCurve W :=
  (existsUnique_splitCompleteNormalization W h₂ h₃ h₄ h₆).choose

/-- The complete split normalization retains its original coefficient map. -/
@[reassoc] theorem splitCompleteNormalization_base :
    splitCompleteNormalization W h₂ h₃ h₄ h₆ ≫ integralCurveStructure W = toBase K :=
  (existsUnique_splitCompleteNormalization W h₂ h₃ h₄ h₆).choose_spec.1.1

/-- The whole affine chart, including both markings, remains unchanged. -/
@[reassoc] theorem splitCompleteNormalization_left :
    left K ≫ splitCompleteNormalization W h₂ h₃ h₄ h₆ =
      splitAffineToCubic W h₂ h₃ h₄ h₆ :=
  (existsUnique_splitCompleteNormalization W h₂ h₃ h₄ h₆).choose_spec.1.2

/-- The complete map is determined by its actual affine coordinates and coefficient map. -/
theorem splitCompleteNormalization_unique (f : scheme K ⟶ integralCurve W)
    (hf : f ≫ integralCurveStructure W = toBase K)
    (hl : left K ≫ f = splitAffineToCubic W h₂ h₃ h₄ h₆) :
    f = splitCompleteNormalization W h₂ h₃ h₄ h₆ :=
  (existsUnique_splitCompleteNormalization W h₂ h₃ h₄ h₆).choose_spec.2 f ⟨hf, hl⟩

end FLT.Mazur
