/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeAmbientChartRefinement
public import FLT.Mazur.DualAtlasChartRefinement

/-!
# Actual projective charts for an ambient sheaf isomorphism

An ambient isomorphism preserves the affine free opens. Its original coordinate
maps commute with every refinement and hence give a cocone on the actual atlas.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasAmbient
open FCurve AffineFiniteFreeAtlas FiniteFreeChartTransitions
open DualFreeSheafCoordinates ProjectiveSpace
variable {X : Scheme.{u}} {M N : X.Modules} (a : M ≅ N)

/-- The same affine open remains a finite free chart after ambient transport. -/
def index (i : Index M) : Index N :=
  ⟨i.val, i.property.1, coordinates M i, inferInstance,
    ⟨(restrictFunctor i.val.ι).mapIso a.symm ≪≫ chart M i⟩⟩

/-- The original free-sheaf change between the chosen coordinates. -/
def change (i : Index M) := ambientChange a (chart M i) (chart N (index a i))

/-- The actual projective chart isomorphism induced by the ambient sheaf isomorphism. -/
def chartIso (i : Index M) := projectiveIso (change a i)

/-- The projective chart changes preserve their actual coefficient projections. -/
@[reassoc]
lemma chartIso_projection (i : Index M) :
    (chartIso a i).hom ≫ affineProjection i.val.toScheme (coordinates N (index a i)) =
      affineProjection i.val.toScheme (coordinates M i) :=
  projectiveIso_projection (change a i)

/-- Original projective chart maps commute with the actual ambient change. -/
lemma chartIso_refinement {i j : Index M} (h : i ≤ j) :
    dualChartInclusion M h (chart M i) (chart M j) ≫ (chartIso a j).hom =
      (chartIso a i).hom ≫ dualChartInclusion N (show index a i ≤ index a j from h)
        (chart N (index a i)) (chart N (index a j)) := by
  change ((projectiveIso (transition M le_rfl h _ _)).hom ≫ _) ≫
      (projectiveIso (change a j)).hom =
    (projectiveIso (change a i)).hom ≫
      (projectiveIso (transition N le_rfl h _ _)).hom ≫ _
  rw [Category.assoc, projectiveIso_pullback,
    ← Category.assoc, ← Iso.trans_hom, ← projectiveIso_trans]
  rw [change, ambientChange_refinement a h (chart M i) (chart M j)
    (chart N (index a i)) (chart N (index a j))]
  rw [projectiveIso_trans, Iso.trans_hom, Category.assoc]
  rfl

/-- Each transported projective chart maps into the original target atlas. -/
def toAtlas (hN : LocallyFiniteFree N) (i : Index M) :
    ProjectiveSpace.space Γ(i.val.toScheme, ⊤) (coordinates M i) ⟶
      LocallyFreeDualProjectiveAtlas.space N hN :=
  (chartIso a i).hom ≫ LocallyFreeDualProjectiveAtlas.chartMap N hN (index a i)

/-- The maps into the target atlas preserve actual base chart inclusions. -/
@[reassoc]
lemma toAtlas_projection (hN : LocallyFiniteFree N) (i : Index M) :
    toAtlas a hN i ≫ LocallyFreeDualProjectiveAtlas.projection N hN =
      affineProjection i.val.toScheme (coordinates M i) ≫ i.val.ι := by
  rw [toAtlas, Category.assoc, LocallyFreeDualProjectiveAtlas.chart_projection]
  exact chartIso_projection_assoc a i i.val.ι

/-- The original transported chart maps descend through all atlas refinements. -/
lemma toAtlas_refinement (hN : LocallyFiniteFree N) {i j : Index M} (h : i ≤ j) :
    dualChartInclusion M h (chart M i) (chart M j) ≫ toAtlas a hN j =
      toAtlas a hN i := by
  rw [toAtlas, ← Category.assoc, chartIso_refinement, Category.assoc,
    LocallyFreeDualProjectiveAtlas.chart_refinement]
  rfl

end FLT.Mazur.DualAtlasAmbient
