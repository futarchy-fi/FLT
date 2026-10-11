/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationOrbitTopology
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.Algebra.Category.Ring.Limits

/-!
# The sheaf of invariant regular functions on the actual orbit space

Both relation maps are pushed to the same orbit space. Their equalizer is a
sheaf of commutative rings, constructed from the original structure sheaves.
No affine neighborhoods or scheme structure are supplied as assumptions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.RelativeRelationOrbit
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q)

/-- The original source structure sheaf pushed onto the orbit space. -/
def sourceSheaf : (space e).Sheaf CommRingCat.{u} :=
  (TopCat.Sheaf.pushforward _ (quotientMap e)).obj U.left.sheaf

/-- The original relation structure sheaf pushed along its first projection. -/
def relationSheaf : (space e).Sheaf CommRingCat.{u} :=
  (TopCat.Sheaf.pushforward _ (p.left.base ≫ quotientMap e)).obj A.left.sheaf

/-- Both relation projections have the same composite to the actual orbit space. -/
theorem relation_quotientMap : p.left.base ≫ quotientMap e = q.left.base ≫ quotientMap e := by
  ext a
  exact projection_pair e a

/-- Pullback of source functions along the first relation projection. -/
def firstRestriction : sourceSheaf e ⟶ relationSheaf e :=
  ⟨(TopCat.Presheaf.pushforward _ (quotientMap e)).map p.left.toPshHom.c⟩

/-- Pullback along the second projection, on the identical orbit open domains. -/
def secondRestriction : sourceSheaf e ⟶ relationSheaf e :=
  ⟨(TopCat.Presheaf.pushforward _ (quotientMap e)).map q.left.toPshHom.c ≫
    (TopCat.Presheaf.pushforwardEq (relation_quotientMap e).symm A.left.presheaf).hom⟩

/-- The actual sheaf of invariant regular functions on the orbit space. -/
def invariantSheaf : (space e).Sheaf CommRingCat.{u} :=
  equalizer (firstRestriction e) (secondRestriction e)

/-- Invariant functions included in all source regular functions. -/
def invariantInclusion : invariantSheaf e ⟶ sourceSheaf e :=
  equalizer.ι (firstRestriction e) (secondRestriction e)

instance invariantInclusion_mono : Mono (invariantInclusion e) :=
  inferInstanceAs (Mono (equalizer.ι (firstRestriction e) (secondRestriction e)))

/-- The included functions agree under the two actual relation pullbacks. -/
theorem invariantInclusion_condition :
    invariantInclusion e ≫ firstRestriction e = invariantInclusion e ≫ secondRestriction e :=
  equalizer.condition _ _

/-- Every compatible family of regular functions factors into the constructed invariant sheaf. -/
def invariantLift {F : (space e).Sheaf CommRingCat.{u}} (a : F ⟶ sourceSheaf e)
    (ha : a ≫ firstRestriction e = a ≫ secondRestriction e) : F ⟶ invariantSheaf e :=
  equalizer.lift a ha

/-- The invariant lift recovers the supplied regular functions. -/
theorem invariantLift_inclusion {F : (space e).Sheaf CommRingCat.{u}}
    (a : F ⟶ sourceSheaf e) (ha) :
    invariantLift e a ha ≫ invariantInclusion e = a := equalizer.lift_ι _ _

/-- Invariant lifts are determined by their source regular functions. -/
theorem invariantLift_unique {F : (space e).Sheaf CommRingCat.{u}}
    (a : F ⟶ sourceSheaf e) (ha) (b : F ⟶ invariantSheaf e)
    (hb : b ≫ invariantInclusion e = a) : b = invariantLift e a ha := by
  apply (cancel_mono (invariantInclusion e)).mp
  rw [hb, invariantLift_inclusion]

/-- The orbit space with its constructed sheaf of invariant commutative rings. -/
def ringedSpace : SheafedSpace CommRingCat.{u} where
  carrier := space e
  presheaf := (invariantSheaf e).obj
  IsSheaf := (invariantSheaf e).property

/-- The original source maps to the constructed ringed orbit space. -/
def toRingedSpace : U.left.toSheafedSpace ⟶ ringedSpace e :=
  ⟨quotientMap e, (invariantInclusion e).hom⟩

end FLT.Mazur.RelativeRelationOrbit
