/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassGeneralizedPointedComparison
public import FLT.Mazur.WeierstrassCoefficientModelProjection

/-!
# The pointed classification retains the constructed full change

Restoring a pointed admissible comparison agrees with the previously constructed
group comparison. Conjugating by coefficient presentations gives the original
varying full comparison, with its exact group and curve maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassChangeParameter
open WeierstrassIntegralChart GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] coefficientModelIso coefficientModelGroupIso
/-- For an everywhere smooth source, its group map determines a full comparison. -/
theorem smoothFullHom_ext_group {S : Scheme} {E F : GeneralizedEllipticCurve S}
    [Epi E.inclusion] (a b : E ⟶ F) (h : a.group = b.group) : a = b := by
  apply forgetCurve.map_injective
  change a.curve = b.curve
  apply (cancel_epi E.inclusion).mp
  rw [a.inclusion, b.inclusion, h]

variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (hW : IsUnit W.Δ) (hV : IsUnit V.Δ)

/-- The full generalized comparison obtained from the actual pointed change. -/
def changeGeneralizedIso (C : VariableChange R) (h : C • V = W) :
    integralGeneralizedEllipticCurve W hW ≅ integralGeneralizedEllipticCurve V hV :=
  pointedToGeneralized W V hW hV (changePointedComparison W V C h)

/-- The restored full comparison retains the original proper admissible map. -/
theorem changeGeneralizedIso_curve (C : VariableChange R) (h : C • V = W) :
    (changeGeneralizedIso W V hW hV C h).hom.curve.left =
      (integralVariableChangeIso V W C h).hom :=
  pointedToGeneralized_curve W V hW hV _

/-- Its group map is precisely the independently constructed admissible group map. -/
theorem changeGeneralizedIso_group (C : VariableChange R) (h : C • V = W) :
    (changeGeneralizedIso W V hW hV C h).hom.group.left =
      (integralVariableChangeGroupIso V W C h hV hW).hom.hom.hom.hom.left := by
  have hi := (changeGeneralizedIso W V hW hV C h).hom.inclusion
  rw [integralGeneralizedEllipticCurve_inclusion,
    integralGeneralizedEllipticCurve_inclusion] at hi
  erw [Category.id_comp, Category.comp_id] at hi
  rw [← congrArg (fun z ↦ z.left) hi, changeGeneralizedIso_curve,
    integralVariableChangeGroupIso_hom]

variable {A : Type} [CommRing A] [Algebra R A]
  (C : VariableChange A) (h : C • V.map (algebraMap R A) = W.map (algebraMap R A))

/-- The varying full comparison is the coefficient conjugate of the pointed classification. -/
theorem changeBaseGeneralizedIso_eq :
    changeBaseGeneralizedIso W V hW hV C h =
      (coefficientModelIso W hW (algebraMap R A)).symm ≪≫
        changeGeneralizedIso _ _ (coefficientEquation_discriminant W hW _)
          (coefficientEquation_discriminant V hV _) C h ≪≫
            coefficientModelIso V hV (algebraMap R A) := by
  let _ := modelBaseChange_smooth W hW (A := A)
  apply Iso.ext
  apply smoothFullHom_ext_group
  apply Over.OverMorphism.ext
  change (changeBaseGroupIso W V hW hV C h).hom.left =
    (coefficientModelIso W hW (algebraMap R A)).inv.group.left ≫
      (changeGeneralizedIso _ _ _ _ C h).hom.group.left ≫
        (coefficientModelIso V hV (algebraMap R A)).hom.group.left
  rw [changeGeneralizedIso_group]
  unfold coefficientModelIso coefficientModelGroupIso
  rfl

end FLT.Mazur.WeierstrassChangeParameter
