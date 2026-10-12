/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassProjectiveCoefficientSquare
public import FLT.Mazur.WeierstrassVariableChangeCoefficient
public import FLT.Mazur.WeierstrassVariableChangeIntegralIso

/-!
# Proper admissible changes commute with coefficient extension

The commuting ambient projective square identifies the actual morphisms of
proper cubics by their closed embeddings. No smoothness or reducedness is
required, so the comparison also retains arbitrary coefficient specializations.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  (W V : WeierstrassCurve R) (C : VariableChange R) (h : C • W = V)

include h in
/-- The actual changed equation retains its named target after extending coefficients. -/
theorem variableChange_coefficient_equation :
    C.map (algebraMap R S) • W.map (algebraMap R S) = V.map (algebraMap R S) := by
  rw [map_variableChange, h]

/-- The full proper coordinate change commutes with the actual coefficient morphisms. -/
@[reassoc] theorem integralVariableChangeTo_coefficient :
    integralCoefficientMorphism (S := S) V ≫ integralVariableChangeTo W V C h =
      integralVariableChangeTo (W.map (algebraMap R S)) (V.map (algebraMap R S))
          (C.map (algebraMap R S)) (variableChange_coefficient_equation W V C h) ≫
        integralCoefficientMorphism W := by
  apply (cancel_mono (integralProjectiveMap W)).mp
  rw [Category.assoc, integralVariableChangeTo_projectiveMap,
    integralProjectiveMap_coefficient_assoc, Category.assoc,
    WeierstrassVariableChangeLinear.projectiveIso_coefficient,
    ← Category.assoc, ← integralVariableChangeTo_projectiveMap,
    Category.assoc, integralProjectiveMap_coefficient]

/-- The inverse proper comparison also commutes with the original coefficient extension. -/
@[reassoc] theorem integralVariableChangeIso_inv_coefficient :
    (integralVariableChangeIso (W.map (algebraMap R S)) (V.map (algebraMap R S))
        (C.map (algebraMap R S)) (variableChange_coefficient_equation W V C h)).inv ≫
      integralCoefficientMorphism V =
        integralCoefficientMorphism W ≫ (integralVariableChangeIso W V C h).inv := by
  apply (cancel_epi (integralVariableChangeIso (W.map (algebraMap R S))
    (V.map (algebraMap R S)) (C.map (algebraMap R S))
      (variableChange_coefficient_equation W V C h)).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  have hc := integralVariableChangeTo_coefficient (S := S) W V C h
  change integralCoefficientMorphism V ≫ (integralVariableChangeIso W V C h).hom =
    (integralVariableChangeIso (W.map (algebraMap R S)) (V.map (algebraMap R S))
      (C.map (algebraMap R S)) (variableChange_coefficient_equation W V C h)).hom ≫
        integralCoefficientMorphism W at hc
  rw [← Category.assoc, ← hc]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.WeierstrassIntegralChart
