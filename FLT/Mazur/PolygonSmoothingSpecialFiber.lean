/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingRing
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# The arithmetic smoothing chart has the original split-node special fiber

At parameter zero the coordinate algebra is identified with the existing
ring of polynomial pairs agreeing at the origin. Both branch coordinates
are retained. The spectra give actual finitely presented affine charts.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonSmoothing

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (R : Type*) [CommRing R]

/-- At zero the smoothing relation is exactly the original split-node relation. -/
theorem relationIdeal_zero : relationIdeal (0 : R) = PolygonNodePresentation.aRelation := by
  simp only [relationIdeal, relation, map_zero, sub_zero, PolygonNodePresentation.aRelation]

/-- The zero-parameter algebra is the original two-branch equalizer ring. -/
def specialFiberEquiv : ChartRing (0 : R) ≃ₐ[R] PolygonNodeEqualizer.A (R := R) :=
  (Ideal.quotientEquivAlgOfEq R (relationIdeal_zero R)).trans
    PolygonNodePresentation.aQuotientEquiv

/-- The original first branch coordinate is retained by the special-fiber comparison. -/
theorem specialFiberEquiv_left :
    specialFiberEquiv R (leftCoordinate 0) = PolygonNodeLocalization.x := by
  rw [specialFiberEquiv, AlgEquiv.trans_apply, leftCoordinate,
    Ideal.quotientEquivAlgOfEq_mk, PolygonNodePresentation.aQuotientEquiv,
    AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk]
  change PolygonNodePresentation.aPresent (MvPolynomial.X 0) = _
  exact PolygonNodePresentation.aPresent_X_zero

/-- The original second branch coordinate is retained by the special-fiber comparison. -/
theorem specialFiberEquiv_right :
    specialFiberEquiv R (rightCoordinate 0) = PolygonNodeLocalization.y := by
  rw [specialFiberEquiv, AlgEquiv.trans_apply, rightCoordinate,
    Ideal.quotientEquivAlgOfEq_mk, PolygonNodePresentation.aQuotientEquiv,
    AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk]
  change PolygonNodePresentation.aPresent (MvPolynomial.X 1) = _
  exact PolygonNodePresentation.aPresent_X_one

/-- The actual affine arithmetic chart, with smoothing parameter in the base ring. -/
def chart (t : R) : Scheme := Spec (.of (ChartRing t))

/-- The chart's original structure map to the coefficient spectrum. -/
def chartStructure (t : R) : chart R t ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing t)))

instance chartStructure_affine (t : R) : IsAffineHom (chartStructure R t) := by
  dsimp [chartStructure, chart]
  infer_instance

instance chartStructure_finitePresentation (t : R) :
    LocallyOfFinitePresentation (chartStructure R t) := by
  rw [chartStructure, LocallyOfFinitePresentation.SpecMap_iff]
  exact (RingHom.finitePresentation_algebraMap).mpr inferInstance

/-- The zero smoothing chart is the original node scheme, with both branches. -/
def specialFiberIso : PolygonNodeBranches.node R ≅ chart R 0 :=
  Scheme.Spec.mapIso (specialFiberEquiv R).toRingEquiv.toCommRingCatIso.op

/-- The actual node comparison preserves the original arithmetic base. -/
theorem specialFiberIso_base :
    (specialFiberIso R).hom ≫ chartStructure R 0 =
      Spec.map (CommRingCat.ofHom (algebraMap R (PolygonNodeEqualizer.A (R := R)))) := by
  change Spec.map (CommRingCat.ofHom (specialFiberEquiv R).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing (0 : R)))) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (specialFiberEquiv R).toAlgHom.comp_algebraMap

end FLT.Mazur.PolygonSmoothing
