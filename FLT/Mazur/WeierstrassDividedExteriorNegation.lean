/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthNegationBoundaries
public import FLT.Mazur.WeierstrassDividedExteriorStep

/-!
# Extending constructed negatives through retained exteriors

Glue an existing exterior automorphism to the actual next incidence negative.
The two attachment identities have been proved from the actual equations. The
result is again compatible with the next boundary and with its whole chart.
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

/-- Extend the constructed exterior negative across the entire next incidence chart. -/
def Exterior.advanceNegationIso : (E.advance hπ e).carrier ≅ (E.advance hπ e).carrier :=
  asIso (pushout.map E.attach (previousToX hπ d e) E.attach (previousToX hπ d e)
    N.hom (stepXNegationIso e).hom (boundaryNegationIso d).hom hN.symm
    (previousToX_negation hπ d e).symm)

/-- The extension retains the actual preceding exterior automorphism. -/
@[reassoc] theorem Exterior.retained_advanceNegationIso :
    E.retained hπ e ≫ (E.advanceNegationIso hπ e N hN).hom =
      N.hom ≫ E.retained hπ e := by
  simp [Exterior.retained, Exterior.advanceNegationIso]

/-- The extension retains the actual negative on the whole new incidence chart. -/
@[reassoc] theorem Exterior.newX_advanceNegationIso :
    E.newX hπ e ≫ (E.advanceNegationIso hπ e N hN).hom =
      (stepXNegationIso e).hom ≫ E.newX hπ e := by
  simp [Exterior.newX, Exterior.advanceNegationIso]

/-- The extended exterior negative retains the exact next attachment map. -/
@[reassoc] theorem Exterior.advanceNegationIso_attach :
    (boundaryNegationIso e).hom ≫ (E.advance hπ e).attach =
      (E.advance hπ e).attach ≫ (E.advanceNegationIso hπ e N hN).hom := by
  change (boundaryNegationIso e).hom ≫ nextToX e ≫ E.newX hπ e = _
  rw [nextToX_negation_assoc]
  change _ = (nextToX e ≫ E.newX hπ e) ≫ _
  rw [Category.assoc, Exterior.newX_advanceNegationIso]

/-- A compatible exterior negative glues to the entire actual divided chart. -/
def Exterior.wholeNegationIso : E.whole ≅ E.whole :=
  asIso (pushout.map E.attach (boundaryInclusion d) E.attach (boundaryInclusion d)
    N.hom (chartNegationIso d).hom (boundaryNegationIso d).hom hN.symm
    (boundaryNegationIso_inclusion d).symm)

omit [IsDomain R] in
/-- Whole-model negation retains the entire exterior. -/
@[reassoc] theorem Exterior.exteriorChart_wholeNegationIso :
    E.exteriorChart ≫ (E.wholeNegationIso N hN).hom = N.hom ≫ E.exteriorChart :=
  by simp [Exterior.exteriorChart, Exterior.wholeNegationIso]

omit [IsDomain R] in
/-- Whole-model negation retains the exact current divided equation chart. -/
@[reassoc] theorem Exterior.dividedChart_wholeNegationIso :
    E.dividedChart ≫ (E.wholeNegationIso N hN).hom =
      (chartNegationIso d).hom ≫ E.dividedChart := by
  simp [Exterior.dividedChart, Exterior.wholeNegationIso]

/-- Extending an involution across the incidence chart preserves its square. -/
@[reassoc] theorem Exterior.advanceNegationIso_comp (hNN : N.hom ≫ N.hom = 𝟙 _) :
    (E.advanceNegationIso hπ e N hN).hom ≫
      (E.advanceNegationIso hπ e N hN).hom = 𝟙 _ := by
  apply pushout.hom_ext
  · change E.retained hπ e ≫ _ = E.retained hπ e ≫ _
    rw [Exterior.retained_advanceNegationIso_assoc, Exterior.retained_advanceNegationIso,
      ← Category.assoc, hNN, Category.id_comp, Category.comp_id]
  · change E.newX hπ e ≫ _ = E.newX hπ e ≫ _
    rw [Exterior.newX_advanceNegationIso_assoc, Exterior.newX_advanceNegationIso,
      Category.comp_id]
    change (stepXNegationIso e).hom ≫ (stepXNegationIso e).inv ≫ E.newX hπ e = _
    exact Iso.hom_inv_id_assoc _ _

omit [IsDomain R] in
/-- Gluing an exterior involution preserves its square on the entire whole model. -/
@[reassoc] theorem Exterior.wholeNegationIso_comp (hNN : N.hom ≫ N.hom = 𝟙 _) :
    (E.wholeNegationIso N hN).hom ≫ (E.wholeNegationIso N hN).hom = 𝟙 _ := by
  apply E.hom_ext
  · rw [Exterior.exteriorChart_wholeNegationIso_assoc, Exterior.exteriorChart_wholeNegationIso,
      ← Category.assoc, hNN, Category.id_comp, Category.comp_id]
  · rw [Exterior.dividedChart_wholeNegationIso_assoc, Exterior.dividedChart_wholeNegationIso,
      Category.comp_id]
    change (chartNegationIso d).hom ≫ (chartNegationIso d).inv ≫ E.dividedChart = _
    exact Iso.hom_inv_id_assoc _ _

end FLT.Mazur.WeierstrassDividedDepth
