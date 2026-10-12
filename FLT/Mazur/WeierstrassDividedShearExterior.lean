/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedShearNextBoundary
public import FLT.Mazur.WeierstrassDividedExteriorStep

/-!
# Shear comparison through an actual exterior replacement

Compatible exterior isomorphisms extend through the original pushouts.
Both attachments and all original chart contractions are preserved.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} {d : Data W π k} (r : R) (E : Exterior d) (F : Exterior (shearData d r))
  (i : F.carrier ≅ E.carrier)
  (hi : F.attach ≫ i.hom = (shearBoundaryIso d r).hom ≫ E.attach)

/-- Glue an actual exterior shear comparison to the complete divided chart. -/
def shearWholeIso : F.whole ≅ E.whole :=
  asIso (pushout.map F.attach (boundaryInclusion (shearData d r)) E.attach
    (boundaryInclusion d) i.hom (shearChartIso d r).hom (shearBoundaryIso d r).hom
    hi (shearBoundaryIso_inclusion d r).symm)

/-- The whole comparison retains the specified original exterior isomorphism. -/
@[reassoc] theorem shearWholeIso_exterior :
    F.exteriorChart ≫ (shearWholeIso r E F i hi).hom = i.hom ≫ E.exteriorChart := by
  simp [shearWholeIso, Exterior.exteriorChart]

/-- The whole comparison retains the actual divided-chart shear. -/
@[reassoc] theorem shearWholeIso_divided :
    F.dividedChart ≫ (shearWholeIso r E F i hi).hom =
      (shearChartIso d r).hom ≫ E.dividedChart := by
  simp [shearWholeIso, Exterior.dividedChart]

variable [IsDomain R] (hπ : π ≠ 0) (e : Data W π (k + 1))

/-- Extend the actual exterior comparison through one original successive chart. -/
def shearAdvanceIso : (F.advance hπ (shearData e r)).carrier ≅ (E.advance hπ e).carrier :=
  asIso (pushout.map F.attach (previousToX hπ (shearData d r) (shearData e r)) E.attach
    (previousToX hπ d e) i.hom (shearStepXIso e r).hom (shearBoundaryIso d r).hom
    hi (shearStepXIso_previousToX hπ d e r))

/-- Enlargement retains the actual old exterior leg. -/
@[reassoc] theorem shearAdvanceIso_retained :
    F.retained hπ (shearData e r) ≫ (shearAdvanceIso r E F i hi hπ e).hom =
      i.hom ≫ E.retained hπ e := by
  simp [shearAdvanceIso, Exterior.retained]

/-- Enlargement retains the whole original new incidence chart. -/
@[reassoc] theorem shearAdvanceIso_newX :
    F.newX hπ (shearData e r) ≫ (shearAdvanceIso r E F i hi hπ e).hom =
      (shearStepXIso e r).hom ≫ E.newX hπ e := by
  simp [shearAdvanceIso, Exterior.newX]

/-- The constructed next exterior comparison retains its actual next attachment. -/
@[reassoc] theorem shearAdvanceIso_attach :
    (F.advance hπ (shearData e r)).attach ≫ (shearAdvanceIso r E F i hi hπ e).hom =
      (shearBoundaryIso e r).hom ≫ (E.advance hπ e).attach := by
  change (nextToX (shearData e r) ≫ F.newX hπ (shearData e r)) ≫ _ =
    (shearBoundaryIso e r).hom ≫ nextToX e ≫ E.newX hπ e
  rw [Category.assoc, shearAdvanceIso_newX, shearStepXIso_nextToX_assoc]

/-- The enlarged exterior comparison retains the original contraction into the old whole. -/
@[reassoc] theorem shearAdvanceIso_contraction :
    (shearAdvanceIso r E F i hi hπ e).hom ≫ E.exteriorContraction hπ e =
      F.exteriorContraction hπ (shearData e r) ≫ (shearWholeIso r E F i hi).hom := by
  apply pushout.hom_ext
  · change F.retained hπ (shearData e r) ≫ _ = F.retained hπ (shearData e r) ≫ _
    rw [shearAdvanceIso_retained_assoc, Exterior.retained_contraction,
      Exterior.retained_contraction_assoc, shearWholeIso_exterior]
  · change F.newX hπ (shearData e r) ≫ _ = F.newX hπ (shearData e r) ≫ _
    rw [shearAdvanceIso_newX_assoc, Exterior.newX_contraction,
      Exterior.newX_contraction_assoc, shearWholeIso_divided,
      shearStepXIso_contraction_assoc]

/-- The whole successor comparison retains both original contraction legs. -/
@[reassoc] theorem shearAdvanceWholeIso_step :
    (shearWholeIso r (E.advance hπ e) (F.advance hπ (shearData e r))
      (shearAdvanceIso r E F i hi hπ e) (shearAdvanceIso_attach r E F i hi hπ e)).hom ≫
        E.stepContraction hπ e =
      F.stepContraction hπ (shearData e r) ≫ (shearWholeIso r E F i hi).hom := by
  apply Exterior.hom_ext
  · rw [shearWholeIso_exterior_assoc, Exterior.exteriorChart_stepContraction,
      Exterior.exteriorChart_stepContraction_assoc, shearAdvanceIso_contraction]
  · rw [shearWholeIso_divided_assoc, Exterior.dividedChart_stepContraction,
      Exterior.dividedChart_stepContraction_assoc,
      shearWholeIso_divided, shearChartIso_transition_assoc]

end FLT.Mazur.WeierstrassDividedDepth
