/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentCompleteNormalization
public import FLT.Mazur.WeierstrassSplitCompleteNormalization
public import FLT.Mazur.WeierstrassVariableChangeAffineRestriction
public import FLT.Mazur.WeierstrassIntegralCoefficientMap

/-!
# The root normalization is the split normalization followed by the actual shear

The comparison uses the original cubic's variable-change isomorphism and
coefficient morphism. Equality on the full affine chart extends across infinity.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur
open Polynomial ProjectiveLine WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {F : Type} [Field F] (W : WeierstrassCurve F)
  [Fact (Irreducible (nodeTangentPolynomial W))]
  (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0)
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "V" => nodeTangentShear W
local notation "U" => W.map (algebraMap F S)
local notation "s" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "C₀" => (⟨1, 0, s, 0⟩ : WeierstrassCurve.VariableChange S)

include h₃ h₄ h₆ in
/-- The actual root shear has exactly the coefficients needed for split normalization. -/
theorem nodeTangentShear_normalization_coefficients :
    (V).a₂ = 0 ∧ (V).a₃ = 0 ∧ (V).a₄ = 0 ∧ (V).a₆ = 0 := by
  obtain ⟨_, h₂, h₃', h₄', h₆'⟩ := nodeTangentShear_coefficients W
  rw [h₃, map_zero] at h₃' h₄'
  rw [h₄, map_zero, mul_zero, sub_zero] at h₄'
  rw [h₆, map_zero] at h₆'
  exact ⟨h₂, h₃', h₄', h₆'⟩

local notation "h" => nodeTangentShear_normalization_coefficients W h₃ h₄ h₆
local notation "φ" => splitNormalizationChart V (h).1 (h).2.1 (h).2.2.1 (h).2.2.2
local notation "e" => integralVariableChangeIso U V C₀ rfl

/-- Every original affine cubic function agrees after the actual tangent shear. -/
theorem nodeTangentNormalizationChart_eq_split :
    nodeTangentNormalizationChart W h₃ h₄ h₆ =
      ((φ).restrictScalars F).comp
        (((affineVariableChangeMap U V C₀ rfl).restrictScalars F).comp
          (chartCoefficientMap W 2)) := by
  apply WeierstrassIntegralChart.hom_ext
  intro i
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, chartCoefficientMap_coord]
  fin_cases i
  · change nodeTangentNormalizationChart W h₃ h₄ h₆ (coord W 2 0) =
      φ (affineVariableChangeMap U V C₀ rfl (coord U 2 0))
    simp only [affineVariableChangeMap_x, Units.val_one, map_one, one_pow, one_mul,
      map_zero, add_zero, nodeTangentNormalizationChart_coord, Matrix.cons_val_zero,
      splitNormalizationChart_coord, nodeTangentNormalizationX]
  · change nodeTangentNormalizationChart W h₃ h₄ h₆ (coord W 2 1) =
      φ (affineVariableChangeMap U V C₀ rfl (coord U 2 1))
    simp only [affineVariableChangeMap_y, Units.val_one, map_one, one_pow, one_mul,
      map_zero, add_zero, map_add, map_mul, AlgHom.commutes,
      nodeTangentNormalizationChart_coord, Matrix.cons_val_one, Matrix.cons_val_zero,
      splitNormalizationChart_coord, nodeTangentNormalizationY, nodeTangentNormalizationX]
    change (X + Polynomial.C s) * (X * (X + Polynomial.C (V).a₁)) =
      X * (X + Polynomial.C (V).a₁) * X + Polynomial.C s * (X * (X + Polynomial.C (V).a₁))
    ring
  · change nodeTangentNormalizationChart W h₃ h₄ h₆ (coord W 2 2) =
      φ (affineVariableChangeMap U V C₀ rfl (coord U 2 2))
    rw [coord_self, coord_self, map_one, map_one, map_one]

/-- The entire affine root normalization is the split map followed by the actual cubic shear. -/
@[reassoc] theorem nodeTangentAffineToCubic_eq_split :
    nodeTangentAffineToCubic W h₃ h₄ h₆ =
      splitAffineToCubic V (h).1 (h).2.1 (h).2.2.1 (h).2.2.2 ≫
        (e).hom ≫ integralCoefficientMorphism W := by
  rw [splitAffineToCubic, Category.assoc, integralVariableChangeIso_affine_assoc,
    integralCurveChart_coefficientMorphism]
  rw [nodeTangentAffineToCubic, nodeTangentNormalizationChart_eq_split]
  change Spec.map _ ≫ _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _ ≫ _
  simp only [← Spec.map_comp_assoc]
  rfl

/-- The complete original root normalization is the complete split normalization after shearing. -/
theorem nodeTangentCompleteNormalization_eq_split :
    nodeTangentCompleteNormalization W h₃ h₄ h₆ =
      splitCompleteNormalization V (h).1 (h).2.1 (h).2.2.1 (h).2.2.2 ≫
        (e).hom ≫ integralCoefficientMorphism W := by
  refine ext_of_isDominant_of_isSeparated (integralCurveStructure W) ?_ (left S) ?_
  · rw [nodeTangentCompleteNormalization_base, Category.assoc, Category.assoc,
      integralCoefficientMorphism_structure, ← Category.assoc]
    change _ = (_ ≫ integralVariableChangeTo U V C₀ rfl) ≫ _ ≫ _
    rw [Category.assoc, integralVariableChangeTo_structure_assoc,
      splitCompleteNormalization_base_assoc]
  · rw [nodeTangentCompleteNormalization_left, splitCompleteNormalization_left_assoc,
      nodeTangentAffineToCubic_eq_split]

end FLT.Mazur
