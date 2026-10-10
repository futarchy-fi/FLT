/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryRelabelCoordinates

/-!
# Actual proper comparisons for relabeled auxiliary families

Equation equality gives a proper comparison before normalization. Its labeled
section diagrams allow the constructed normalization isomorphism to be used
with any relabeling, without assuming a normalization compatibility law.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (e : MulAut (Labels 4))
  (f : Spec (.of R) ⟶ levelFour.left)

/-- Relabeling identifies the underlying original proper cubic by equation equality. -/
def auxiliaryFamilyRelabelIso :
    integralCurve (auxiliaryPullbackEquation
      (auxiliaryPointSections (f ≫ (auxiliaryAction 4 e).hom))) ≅
        integralCurve (auxiliaryPullbackEquation (auxiliaryPointSections f)) :=
  eqToIso (congrArg integralCurve (auxiliaryPointSections_relabel_equation e f))

/-- The relabeling comparison preserves the coefficient spectrum. -/
theorem auxiliaryFamilyRelabelIso_base :
    (auxiliaryFamilyRelabelIso e f).hom ≫
      integralCurveStructure (auxiliaryPullbackEquation (auxiliaryPointSections f)) =
        integralCurveStructure (auxiliaryPullbackEquation
          (auxiliaryPointSections (f ≫ (auxiliaryAction 4 e).hom))) :=
  auxiliaryEquationTransport_structure (auxiliaryPointSections_relabel_equation e f)

/-- The relabeling comparison preserves the original zero section. -/
theorem auxiliaryFamilyRelabelIso_zero :
    integralCurveZero (auxiliaryPullbackEquation
      (auxiliaryPointSections (f ≫ (auxiliaryAction 4 e).hom))) ≫
        (auxiliaryFamilyRelabelIso e f).hom =
          integralCurveZero (auxiliaryPullbackEquation (auxiliaryPointSections f)) :=
  auxiliaryEquationTransport_zero (auxiliaryPointSections_relabel_equation e f)

/-- Its labeled sections are exactly the original sections with inverse labels. -/
theorem auxiliaryFamilyRelabelIso_mark (a : Labels 4) (ha : a ≠ 1) :
    auxiliaryPullbackSection (auxiliaryPointSections (f ≫ (auxiliaryAction 4 e).hom)) a ha ≫
      (auxiliaryFamilyRelabelIso e f).hom =
        auxiliaryPullbackSection (auxiliaryPointSections f) (e.symm a)
          (auxiliaryRelabel_ne_one e a ha) := by
  apply auxiliaryEquationTransport_section (auxiliaryPointSections_relabel_equation e f)
  intro i
  rw [auxiliaryPullbackEvaluation_coord, auxiliaryPullbackEvaluation_coord,
    auxiliaryPointSections_relabel_coordinate]

/-- A proper comparison remains an actual proper comparison after relabeling both families. -/
def auxiliaryRelabeledComparison (g : Spec (.of R) ⟶ levelFour.left)
    (c : integralCurve (auxiliaryPullbackEquation (auxiliaryPointSections f)) ≅
      integralCurve (auxiliaryPullbackEquation (auxiliaryPointSections g))) :
    integralCurve (auxiliaryPullbackEquation
      (auxiliaryPointSections (f ≫ (auxiliaryAction 4 e).hom))) ≅
        integralCurve (auxiliaryPullbackEquation
          (auxiliaryPointSections (g ≫ (auxiliaryAction 4 e).hom))) :=
  auxiliaryFamilyRelabelIso e f ≪≫ c ≪≫ (auxiliaryFamilyRelabelIso e g).symm

variable (g : Spec (.of R) ⟶ levelFour.left)
  (c : integralCurve (auxiliaryPullbackEquation (auxiliaryPointSections f)) ≅
    integralCurve (auxiliaryPullbackEquation (auxiliaryPointSections g)))

/-- Relabeling transports the base diagram of the original comparison. -/
theorem auxiliaryRelabeledComparison_base
    (hb : c.hom ≫ integralCurveStructure (auxiliaryPullbackEquation (auxiliaryPointSections g)) =
      integralCurveStructure (auxiliaryPullbackEquation (auxiliaryPointSections f))) :
    (auxiliaryRelabeledComparison e f g c).hom ≫
      integralCurveStructure (auxiliaryPullbackEquation
        (auxiliaryPointSections (g ≫ (auxiliaryAction 4 e).hom))) =
          integralCurveStructure (auxiliaryPullbackEquation
            (auxiliaryPointSections (f ≫ (auxiliaryAction 4 e).hom))) := by
  simp only [auxiliaryRelabeledComparison, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    ← auxiliaryFamilyRelabelIso_base e g, Iso.inv_hom_id_assoc, hb]
  exact auxiliaryFamilyRelabelIso_base e f

/-- Relabeling transports the zero diagram of the original comparison. -/
theorem auxiliaryRelabeledComparison_zero
    (hz : integralCurveZero (auxiliaryPullbackEquation (auxiliaryPointSections f)) ≫ c.hom =
      integralCurveZero (auxiliaryPullbackEquation (auxiliaryPointSections g))) :
    integralCurveZero (auxiliaryPullbackEquation
      (auxiliaryPointSections (f ≫ (auxiliaryAction 4 e).hom))) ≫
        (auxiliaryRelabeledComparison e f g c).hom =
          integralCurveZero (auxiliaryPullbackEquation
            (auxiliaryPointSections (g ≫ (auxiliaryAction 4 e).hom))) := by
  apply (cancel_mono (auxiliaryFamilyRelabelIso e g).hom).mp
  simp only [auxiliaryRelabeledComparison, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, auxiliaryFamilyRelabelIso_zero, hz, auxiliaryFamilyRelabelIso_zero]

/-- All original label diagrams transport to the relabeled comparison. -/
theorem auxiliaryRelabeledComparison_mark
    (hm : ∀ (a : Labels 4) (ha : a ≠ 1),
      auxiliaryPullbackSection (auxiliaryPointSections f) a ha ≫ c.hom =
        auxiliaryPullbackSection (auxiliaryPointSections g) a ha)
    (a : Labels 4) (ha : a ≠ 1) :
    auxiliaryPullbackSection (auxiliaryPointSections (f ≫ (auxiliaryAction 4 e).hom)) a ha ≫
      (auxiliaryRelabeledComparison e f g c).hom =
        auxiliaryPullbackSection (auxiliaryPointSections (g ≫ (auxiliaryAction 4 e).hom)) a ha := by
  apply (cancel_mono (auxiliaryFamilyRelabelIso e g).hom).mp
  simp only [auxiliaryRelabeledComparison, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, auxiliaryFamilyRelabelIso_mark, hm, auxiliaryFamilyRelabelIso_mark]

end FLT.Mazur.UniversalWeierstrass
