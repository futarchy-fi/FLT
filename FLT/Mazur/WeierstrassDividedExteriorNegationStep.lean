/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedExteriorNegation

/-!
# The extended negative retains the exact whole successor contraction

Check the old exterior, the new incidence chart and the new divided chart.
Their original contractions agree with the already constructed negatives,
so the entire next whole model retains the actual preceding whole morphism.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} {k : ℕ} (hπ : π ≠ 0)
  {d : Data W π k} (E : Exterior d) (e : Data W π (k + 1))
  (N : E.carrier ≅ E.carrier)
  (hN : (boundaryNegationIso d).hom ≫ E.attach = E.attach ≫ N.hom)

/-- The enlarged exterior negative keeps the exact exterior-to-whole contraction. -/
@[reassoc] theorem Exterior.advanceNegationIso_contraction :
    (E.advanceNegationIso hπ e N hN).hom ≫ E.exteriorContraction hπ e =
      E.exteriorContraction hπ e ≫ (E.wholeNegationIso N hN).hom := by
  apply pushout.hom_ext
  · change E.retained hπ e ≫ _ = E.retained hπ e ≫ _
    rw [Exterior.retained_advanceNegationIso_assoc, Exterior.retained_contraction,
      Exterior.retained_contraction_assoc, Exterior.exteriorChart_wholeNegationIso]
  · change E.newX hπ e ≫ _ = E.newX hπ e ≫ _
    rw [Exterior.newX_advanceNegationIso_assoc, Exterior.newX_contraction,
      Exterior.newX_contraction_assoc, Exterior.dividedChart_wholeNegationIso,
      stepXNegationIso_contraction_assoc]

/-- The complete successor negative retains the actual preceding whole model map. -/
@[reassoc] theorem Exterior.wholeNegationIso_step :
    ((E.advance hπ e).wholeNegationIso (E.advanceNegationIso hπ e N hN)
        (E.advanceNegationIso_attach hπ e N hN)).hom ≫ E.stepContraction hπ e =
      E.stepContraction hπ e ≫ (E.wholeNegationIso N hN).hom := by
  apply (E.advance hπ e).hom_ext
  · rw [Exterior.exteriorChart_wholeNegationIso_assoc,
      Exterior.exteriorChart_stepContraction, Exterior.exteriorChart_stepContraction_assoc,
      Exterior.advanceNegationIso_contraction]
  · rw [Exterior.dividedChart_wholeNegationIso_assoc,
      Exterior.dividedChart_stepContraction, Exterior.dividedChart_stepContraction_assoc,
      Exterior.dividedChart_wholeNegationIso, chartNegationIso_transition_assoc]

end FLT.Mazur.WeierstrassDividedDepth
