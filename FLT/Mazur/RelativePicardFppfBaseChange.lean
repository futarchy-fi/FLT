/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativePicardFppfSheaf
public import FLT.Mazur.RelativePicardPresheafBaseChange

/-!
# The relative Picard fppf sheaf commutes with change of the fixed base

Restriction from the big fppf site over S to that over S' commutes with
sheafification. Combined with the actual fiber-product comparison, this
identifies the Picard sheaf of X ×[S] S' with the restriction of that of X.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemePicard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
local instance : Limits.HasColimitsOfSize.{u + 1, u + 1} CommGrpCat.{u + 1} :=
  Adjunction.has_colimits_of_equivalence commGroupAddCommGroupEquivalence.functor
variable {X S S' : Scheme.{u}} (f : X ⟶ S) (a : S' ⟶ S)

/-- Restrict an fppf group sheaf to test schemes over the new fixed base. -/
def relativeFppfRestriction :
    Sheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1} ⥤
      Sheaf (Scheme.fppfTopology.over S') CommGrpCat.{u + 1} :=
  (Over.map a).sheafPushforwardContinuous CommGrpCat.{u + 1}
    (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S)

/-- The relative Picard sheaf is compatible with every change of the fixed base. -/
def relativeFppfBaseChange :
    (relativeFppfRestriction a).obj (relativeFppfSheaf f) ≅
      relativeFppfSheaf (Limits.pullback.snd f a) :=
  ((Over.map a).pushforwardContinuousSheafificationCompatibility CommGrpCat.{u + 1}
    (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S)).symm.app
      (relativePresheaf f) ≪≫
    (presheafToSheaf (Scheme.fppfTopology.over S') CommGrpCat.{u + 1}).mapIso
      (relativePresheafBaseChange f a)

/-- Fixed-base comparison retains the canonical map from relative line-bundle classes. -/
@[reassoc]
lemma relativeFppfBaseChange_comparison :
    Functor.whiskerLeft (Over.map a).op (relativeFppfComparison f) ≫
        (relativeFppfBaseChange f a).hom.hom =
      (relativePresheafBaseChange f a).hom ≫
        relativeFppfComparison (Limits.pullback.snd f a) := by
  let e : sheafify (Scheme.fppfTopology.over S')
      ((Over.map a).op ⋙ relativePresheaf f) ≅
      (Over.map a).op ⋙ sheafify (Scheme.fppfTopology.over S) (relativePresheaf f) :=
    (sheafToPresheaf (Scheme.fppfTopology.over S') CommGrpCat.{u + 1}).mapIso
      (((Over.map a).pushforwardContinuousSheafificationCompatibility
        CommGrpCat.{u + 1} (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S)).app
          (relativePresheaf f))
  have h := (Over.map a).toSheafify_pullbackSheafificationCompatibility
    CommGrpCat.{u + 1} (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S)
      (relativePresheaf f)
  change toSheafify _ _ ≫ e.hom = _ at h
  change Functor.whiskerLeft (Over.map a).op (toSheafify _ _) ≫
    (e.inv ≫ sheafifyMap _ (relativePresheafBaseChange f a).hom) = _
  rw [← h, Category.assoc, ← Category.assoc e.hom, e.hom_inv_id, Category.id_comp]
  exact (toSheafify_naturality (Scheme.fppfTopology.over S')
    (relativePresheafBaseChange f a).hom).symm

end FLT.Mazur.SchemePicard
