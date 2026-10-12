/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineValuationExtension
public import FLT.Mazur.NodeTangentProjectiveLineDescent
public import FLT.Mazur.WeierstrassIntegralProper

/-!
# The complete root normalization maps to the original cubic

Proper extension constructs the missing morphism across infinity. Its entire
left chart is the original root-sheared coordinate map, and uniqueness promotes
the affine conjugation equality to an equality on the complete line.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur
open ProjectiveLine WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {F : Type u} [Field F] (W : WeierstrassCurve F)
  [Fact (Irreducible (nodeTangentPolynomial W))]
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap F S))
local notation "σ" => RingEquiv.toRingHom (AlgEquiv.toRingEquiv (nodeTangentConjugation W))
variable (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0)

/-- The original affine normalization, with the original projective chart inclusion. -/
def nodeTangentAffineToCubic : chart S ⟶ integralCurve W :=
  Spec.map (CommRingCat.ofHom (nodeTangentNormalizationChart W h₃ h₄ h₆).toRingHom) ≫
    integralCurveChart W 2

/-- The original affine map retains its coefficient projection. -/
@[reassoc] theorem nodeTangentAffineToCubic_base :
    nodeTangentAffineToCubic W h₃ h₄ h₆ ≫ integralCurveStructure W =
      left S ≫ toBase S ≫ b := by
  rw [nodeTangentAffineToCubic, Category.assoc, integralCurveChart_structure,
    chartStructure, specAlgHom_structure, left_toBase_assoc]
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- Properness constructs the complete extension of the actual normalization map. -/
theorem nodeTangent_existsUnique_completeNormalization :
    ∃! f : scheme S ⟶ integralCurve W,
      f ≫ integralCurveStructure W = toBase S ≫ b ∧
        left S ≫ f = nodeTangentAffineToCubic W h₃ h₄ h₆ :=
  existsUnique_left_extension S (toBase S ≫ b) (integralCurveStructure W)
    (nodeTangentAffineToCubic W h₃ h₄ h₆) (nodeTangentAffineToCubic_base W h₃ h₄ h₆)

/-- The actual complete projective normalization morphism into the original cubic. -/
def nodeTangentCompleteNormalization : scheme S ⟶ integralCurve W :=
  (nodeTangent_existsUnique_completeNormalization W h₃ h₄ h₆).choose

/-- The complete extension retains the original coefficient morphism. -/
@[reassoc] theorem nodeTangentCompleteNormalization_base :
    nodeTangentCompleteNormalization W h₃ h₄ h₆ ≫ integralCurveStructure W =
      toBase S ≫ b :=
  (nodeTangent_existsUnique_completeNormalization W h₃ h₄ h₆).choose_spec.1.1

/-- The entire original normalization chart is retained, including both node preimages. -/
@[reassoc] theorem nodeTangentCompleteNormalization_left :
    left S ≫ nodeTangentCompleteNormalization W h₃ h₄ h₆ =
      nodeTangentAffineToCubic W h₃ h₄ h₆ :=
  (nodeTangent_existsUnique_completeNormalization W h₃ h₄ h₆).choose_spec.1.2

/-- Actual affine conjugation preserves the full map into the original cubic. -/
@[reassoc] theorem nodeTangentAffineToCubic_conjugation :
    Spec.map (CommRingCat.ofHom (nodeTangentNormalizationConjugation W).toRingHom) ≫
      nodeTangentAffineToCubic W h₃ h₄ h₆ = nodeTangentAffineToCubic W h₃ h₄ h₆ := by
  rw [nodeTangentAffineToCubic, ← Category.assoc, ← Spec.map_comp]
  have h := congrArg AlgHom.toRingHom
    (nodeTangentNormalizationConjugation_chart W h₃ h₄ h₆)
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f) ≫ integralCurveChart W 2) h

/-- The constructed complete conjugation fixes the original cubic projection across infinity. -/
@[reassoc] theorem nodeTangentCompleteNormalization_conjugation :
    nodeTangentLineConjugation W ≫ nodeTangentCompleteNormalization W h₃ h₄ h₆ =
      nodeTangentCompleteNormalization W h₃ h₄ h₆ := by
  refine ext_of_isDominant_of_isSeparated (integralCurveStructure W) ?_ (left S) ?_
  · rw [Category.assoc, nodeTangentCompleteNormalization_base,
      nodeTangentLineConjugation_base_assoc]
    congr 1
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext (nodeTangentConjugation W).commutes)
  · rw [nodeTangentLineConjugation_left_assoc, nodeTangentCompleteNormalization_left,
      nodeTangentAffineToCubic_conjugation]

end FLT.Mazur
