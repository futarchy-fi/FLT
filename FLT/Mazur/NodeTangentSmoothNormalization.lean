/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentNormalizationInfinity
public import FLT.Mazur.ProjectiveLineSlopeNormalizationCharts
public import FLT.Mazur.PolygonAtlasSmoothLocus

/-!
# The full ordered exterior torus retains the original smooth curve

The complete root normalization restricts to the actual root-sheared smooth
parameter, with the reciprocal Laurent orientation forced by its markings.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur
open WeierstrassIntegralChart WeierstrassDividedDepth ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

/-- The complete split normalization retains the full torus through any actual variable change. -/
@[reassoc] theorem splitNormalization_variableChange_torus
    {K : Type} [Field K] (U V : WeierstrassCurve K) (a : Kˣ)
    (C : WeierstrassCurve.VariableChange K) (h : C • U = V)
    (he : V = splitNodalEquation a)
    (h2 : V.a₂ = 0) (h3 : V.a₃ = 0) (h4 : V.a₄ = 0) (h6 : V.a₆ = 0) :
    infinityTorusChart a ≫ splitCompleteNormalization V h2 h3 h4 h6 ≫
        (integralVariableChangeIso U V C h).hom =
      splitNodalTorusToCurve a ≫
        (integralVariableChangeIso U (splitNodalEquation a) C (h.trans he)).hom := by
  cases he
  rw [splitCompleteNormalization_infinity_assoc]

variable {F : Type} [Field F] (W : WeierstrassCurve F)
  [Fact (Irreducible (nodeTangentPolynomial W))]
  (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial W)
local notation "U" => W.map (algebraMap F Q)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "h3" => show (U).a₃ = 0 from by simp only [WeierstrassCurve.map_a₃, h₃, map_zero]
local notation "h4" => show (U).a₄ = 0 from by simp only [WeierstrassCurve.map_a₄, h₄, map_zero]
local notation "h6" => show (U).a₆ = 0 from by simp only [WeierstrassCurve.map_a₆, h₆, map_zero]
variable (a : (AdjoinRoot (nodeTangentPolynomial W))ˣ)
  (ha : (a : AdjoinRoot (nodeTangentPolynomial W)) = (nodeTangentShear W).a₁)
local notation "ha'" => ha.trans (nodeTangentShear_coefficients W).1
local notation "I" => rootShearTorusSmoothIso U r a ha' (nodeTangentRoot_equation W) h3 h4 h6

/-- The whole original infinity torus contracts by its actual root-sheared smooth parameter. -/
@[reassoc] theorem nodeTangentNormalization_infinityTorus_smooth :
    infinityTorusChart a ≫ nodeTangentCompleteNormalization W h₃ h₄ h₆ =
      (I).hom ≫ (integralSmoothOpen U).ι ≫ integralCoefficientMorphism W := by
  rw [nodeTangentCompleteNormalization_eq_split, rootShearTorusSmoothIso_inclusion_assoc]
  exact splitNormalization_variableChange_torus_assoc U (nodeTangentShear W) a _ rfl
    (rootShearCurve_eq_splitNodal U r a ha' (nodeTangentRoot_equation W) h3 h4 h6)
    _ _ _ _ _

/-- The ordered punctured exterior is the same entire smooth torus in reciprocal coordinates. -/
@[reassoc] theorem nodeTangentNormalization_orderedTorus_smooth :
    (inversion Q).hom ≫ (PolygonPinching.torusToComponent Q).left ≫
        (slopeNormalizationIso a).inv ≫ nodeTangentCompleteNormalization W h₃ h₄ h₆ =
      (I).hom ≫ (integralSmoothOpen U).ι ≫ integralCoefficientMorphism W := by
  change (inversion Q).hom ≫ overlapLeft Q ≫ left Q ≫ _ ≫ _ = _
  rw [← Category.assoc, ← overlapRight, ← Category.assoc,
    ← slopeNormalization_infinityTorus_left, Category.assoc, Iso.hom_inv_id_assoc]
  exact nodeTangentNormalization_infinityTorus_smooth W h₃ h₄ h₆ a ha

end FLT.Mazur
