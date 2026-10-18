/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassChangePointedGeneralizedIso
public import FLT.Mazur.WeierstrassVariableChangeProperCoefficient
public import FLT.Mazur.GeneralizedCurveBaseChangeCoherence

/-!
# Full admissible comparisons commute with coefficient specialization

The original proper coefficient square lifts to equality in the full DR
category. The proof uses the actual maps, including group and action.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassChangeParameter
open WeierstrassIntegralChart GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] coefficientModelIso changeGeneralizedIso

/-- An original-curve projection square determines the full pullback square. -/
theorem fullCoefficientSquare {S T : Scheme} (E F : GeneralizedEllipticCurve S)
    (D H : GeneralizedEllipticCurve T) (g : T ⟶ S)
    (a : D ⟶ E.baseChange g) (b : H ⟶ F.baseChange g) (c : E ⟶ F) (d : D ⟶ H)
    (h : (a.curve.left ≫ pullback.fst _ g) ≫ c.curve.left =
      d.curve.left ≫ (b.curve.left ≫ pullback.fst _ g)) :
    a ≫ baseChangeMap g c = d ≫ b := by
  apply baseChange_hom_ext
  change a.curve.left ≫ (baseChangeMap g c).curve.left ≫ pullback.fst _ g =
    d.curve.left ≫ b.curve.left ≫ pullback.fst _ g
  rw [baseChangeMap_fst]
  exact (Category.assoc _ _ _).symm.trans h

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
  (W V : WeierstrassCurve R) (hW : IsUnit W.Δ) (hV : IsUnit V.Δ)
  (C : VariableChange R) (h : C • V = W)
local notation "f" => algebraMap R A
local notation "hW'" => coefficientEquation_discriminant W hW f
local notation "hV'" => coefficientEquation_discriminant V hV f

/-- Arbitrary coefficient specialization commutes with the entire admissible comparison. -/
theorem changeGeneralizedIso_natural :
    (coefficientModelIso W hW f).hom ≫
      baseChangeMap (Spec.algebraMap R A) (changeGeneralizedIso W V hW hV C h).hom =
    (changeGeneralizedIso (W.map f) (V.map f) hW' hV' (C.map f)
      (variableChange_coefficient_equation V W C h)).hom ≫
        (coefficientModelIso V hV f).hom := by
  apply fullCoefficientSquare
  erw [coefficientModelIso_fst W hW f, coefficientModelIso_fst V hV f]
  rw [changeGeneralizedIso_curve, changeGeneralizedIso_curve]
  change (𝟙 _ ≫ integralCoefficientMorphism W) ≫ (integralVariableChangeIso V W C h).hom =
    (integralVariableChangeIso (V.map f) (W.map f) (C.map f)
      (variableChange_coefficient_equation V W C h)).hom ≫
        (𝟙 _ ≫ integralCoefficientMorphism V)
  simp only [Category.id_comp]
  exact integralVariableChangeTo_coefficient V W C h

/-- Named specialized equations retain the same full coefficient square. -/
theorem changePresentationIso_natural
    (W' V' : WeierstrassCurve A) (hU : IsUnit W'.Δ) (hZ : IsUnit V'.Δ)
    (hw : W' = W.map f) (hv : V' = V.map f)
    (C' : VariableChange A) (hc : C' = C.map f) (h' : C' • V' = W') :
    (coefficientPresentationIso W hW f W' hU hw).hom ≫
      baseChangeMap (Spec.algebraMap R A) (changeGeneralizedIso W V hW hV C h).hom =
    (changeGeneralizedIso W' V' hU hZ C' h').hom ≫
      (coefficientPresentationIso V hV f V' hZ hv).hom := by
  subst W' V' C'
  simpa only [coefficientPresentationIso, eqToIso_refl, Iso.refl_trans] using
    changeGeneralizedIso_natural (A := A) W V hW hV C h

end FLT.Mazur.WeierstrassChangeParameter
