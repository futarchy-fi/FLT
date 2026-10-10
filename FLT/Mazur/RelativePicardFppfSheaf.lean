/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativePicardPresheaf
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Over

/-!
# The relative Picard sheaf on the big fppf site

Sheafification of the relative Picard quotient presheaf gives a commutative
group sheaf. Its comparison retains the actual line-bundle representatives
and their restriction maps. No representability claim is made here.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.SchemePicard
local instance : Limits.HasColimitsOfSize.{u + 1, u + 1} CommGrpCat.{u + 1} :=
  Adjunction.has_colimits_of_equivalence commGroupAddCommGroupEquivalence.functor

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The relative Picard group sheaf for the big fppf site over the base scheme. -/
def relativeFppfSheaf : Sheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1} :=
  (presheafToSheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1}).obj (relativePresheaf f)

/-- The canonical comparison from relative line-bundle classes to the Picard sheaf. -/
def relativeFppfComparison : relativePresheaf f ⟶ (relativeFppfSheaf f).obj :=
  toSheafify (Scheme.fppfTopology.over S) (relativePresheaf f)

/-- The section represented by a relative line-bundle class. -/
def relativeFppfClass (T : Over S) :
    RelativePic (Limits.pullback.snd f T.hom) →*
      (relativeFppfSheaf f).obj.obj (op T) :=
  ((relativeFppfComparison f).app (op T)).hom

/-- Restricting a represented section pulls back its relative class. -/
lemma relativeFppfClass_naturality {T U : Over S} (g : T ⟶ U)
    (a : RelativePic (Limits.pullback.snd f U.hom)) :
    (relativeFppfSheaf f).obj.map g.op (relativeFppfClass f U a) =
      relativeFppfClass f T (relativeBaseMap f g a) :=
  ((relativeFppfComparison f).naturality_apply g.op a).symm

/-- Tensoring a representative by a line bundle from the base has no effect in the sheaf. -/
lemma relativeFppfClass_base_twist (T : Over S)
    (a : Pic (Limits.pullback f T.hom)) (b : Pic T.left) :
    relativeFppfClass f T
        (relativeClass (Limits.pullback.snd f T.hom)
          (a * pullback (Limits.pullback.snd f T.hom) b)) =
      relativeFppfClass f T (relativeClass (Limits.pullback.snd f T.hom) a) := by
  rw [relativeClass_base_twist]

/-- Every map from relative classes into an fppf group sheaf factors through the comparison. -/
def relativeFppfLift (Q : Sheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1})
    (η : relativePresheaf f ⟶ Q.obj) : (relativeFppfSheaf f).obj ⟶ Q.obj :=
  sheafifyLift (Scheme.fppfTopology.over S) η Q.property

/-- The universal lift agrees with the original map on every relative class. -/
@[reassoc]
lemma relativeFppfComparison_lift
    (Q : Sheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1})
    (η : relativePresheaf f ⟶ Q.obj) :
    relativeFppfComparison f ≫ relativeFppfLift f Q η = η :=
  toSheafify_sheafifyLift (Scheme.fppfTopology.over S) η Q.property

/-- The comparison uniquely determines maps from the relative Picard sheaf. -/
lemma relativeFppfLift_unique
    (Q : Sheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1})
    (η : relativePresheaf f ⟶ Q.obj) (γ : (relativeFppfSheaf f).obj ⟶ Q.obj)
    (h : relativeFppfComparison f ≫ γ = η) : γ = relativeFppfLift f Q η :=
  sheafifyLift_unique (Scheme.fppfTopology.over S) η Q.property γ h

end FLT.Mazur.SchemePicard
