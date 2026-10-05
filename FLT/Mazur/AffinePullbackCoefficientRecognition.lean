/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineModulePullbackSections

/-!
# Recognizing a sheaf reconstruction from its coefficient chart

The affine scalar-extension chart lifts back to the original pullback
isomorphism under tilde. This records the counit coherence needed to recognize
candidate descended sheaves from their coefficient coalgebras.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffinePullbackCoefficientRecognition
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem counit_chart {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G) {X : C} {Y : D} (f : L.obj X ⟶ Y) :
    L.map (adj.unit.app X ≫ G.map f) ≫ adj.counit.app Y = f := by
  have hn := adj.counit.naturality f
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  erw [Functor.map_comp, Category.assoc, hn,
    ← Category.assoc, adj.left_triangle_components, Category.id_comp]

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
variable (A : (Spec R).Modules) [A.IsQuasicoherent]
variable {M : (Spec S).Modules} (e : (pullback (Spec.map φ)).obj A ≅ M)

/-- The coefficient chart of a proposed geometric reconstruction. -/
def chart :
    (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj A) ≅
      moduleSpecΓFunctor.obj M :=
  AffineModulePullbackSections.sectionsIso φ A ≪≫ moduleSpecΓFunctor.mapIso e

/-- The scalar-extension section chart lifts to the actual sheaf pullback chart. -/
@[reassoc]
theorem sectionsIso_counit :
    (tilde.functor S).map (AffineModulePullbackSections.sectionsIso φ A).hom ≫
        ((pullback (Spec.map φ)).obj A).fromTildeΓ =
      (AffineModulePullbackSections.pullbackIso φ A).hom := by
  exact counit_chart tilde.adjunction (AffineModulePullbackSections.pullbackIso φ A).hom

/-- Lifting the coefficient chart recovers the given geometric reconstruction. -/
@[reassoc]
theorem chart_counit :
    (tilde.functor S).map (chart φ A e).hom ≫ M.fromTildeΓ =
      ((AffineModulePullbackSections.tildePullbackIso φ).app
        (moduleSpecΓFunctor.obj A)).hom ≫
        (pullback (Spec.map φ)).map A.fromTildeΓ ≫ e.hom := by
  have hn := fromTildeΓNatTrans.naturality e.hom
  change (tilde.functor S).map (moduleSpecΓFunctor.map e.hom) ≫ M.fromTildeΓ =
    ((pullback (Spec.map φ)).obj A).fromTildeΓ ≫ e.hom at hn
  dsimp only [chart, Iso.trans_hom, Functor.mapIso_hom]
  rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc, sectionsIso_counit]
  rfl

end FLT.Mazur.AffinePullbackCoefficientRecognition
