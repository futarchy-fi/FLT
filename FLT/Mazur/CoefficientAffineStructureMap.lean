/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientAffineRingSystem

/-!
# Structure maps in the actual affine coefficient ring system

The projections of the actual scheme pullbacks induce a natural transformation
from the coefficient rings to their model coordinate rings. The original-base
projection gives the compatible map of their colimit rings.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CoefficientAffineStructureMap
open Approximation CoefficientAffineRingSystem
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {A : Type u} [CommRing A] (R : Subalgebra ℤ A)
  {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R))

/-- The actual projection of each coefficient model to its affine coefficient base. -/
abbrev projection (i : CoefficientStage R) :=
  (schemeBaseChangeProjection (coefficientSpectrumToInitial R) q).app (.op i)

/-- The coefficient-to-model structure maps retain naturality of the scheme projections. -/
def structureMap : coefficientStageDiagram R ⟶ diagram R q where
  app i := (Scheme.ΓSpecIso (.of i.val)).inv ≫ (projection R q i).appTop
  naturality i j f := by
    change CommRingCat.ofHom (Subalgebra.inclusion (leOfHom f)).toRingHom ≫
      (Scheme.ΓSpecIso (.of j.val)).inv ≫ (projection R q j).appTop =
      ((Scheme.ΓSpecIso (.of i.val)).inv ≫ (projection R q i).appTop) ≫
        ((coefficientModelDiagram R q).map f.op).appTop
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      Category.assoc, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]
    congr 1
    exact congrArg Scheme.Hom.appTop
      ((schemeBaseChangeProjection (coefficientSpectrumToInitial R) q).naturality f.op).symm

/-- The structure map of the model pulled back to the original affine base. -/
def originalMap : A →+* (cocone R q).pt :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫
    (pullback.snd q (Spec.map (CommRingCat.ofHom R.val.toRingHom))).appTop).hom

/-- The actual coordinate cocones commute with the original-base structure map. -/
theorem cocone_square (i : CoefficientStage R) :
    ((cocone R q).ι.app i).hom.comp ((structureMap R q).app i).hom =
      (originalMap R q).comp ((coefficientStageCocone R).ι.app i).hom := by
  apply CommRingCat.hom_ext_iff.mp
  change ((Scheme.ΓSpecIso (.of i.val)).inv ≫ (projection R q i).appTop) ≫
    ((coefficientModelCone R q).π.app (.op i)).appTop =
    CommRingCat.ofHom i.val.val.toRingHom ≫ (Scheme.ΓSpecIso (.of A)).inv ≫
      (pullback.snd q (Spec.map (CommRingCat.ofHom R.val.toRingHom))).appTop
  erw [Category.assoc, ← Scheme.Hom.comp_appTop,
    (coefficientModelCone_isPullback R q (.op i)).w,
    Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  exact Category.assoc _ _ _

end FLT.Mazur.CoefficientAffineStructureMap
