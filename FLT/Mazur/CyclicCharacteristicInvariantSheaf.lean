/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicOrbitTopology
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
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
variable (n : ℕ) [NeZero n]
local notation "U" => normalizedDisjointSource n
local notation "A" => disjointComparisonArrows n
local notation "src" => disjointComparisonSource n
local notation "tgt" => disjointComparisonTarget n

/-- The original source structure sheaf pushed onto the orbit space. -/
def sourceSheaf : (space n).Sheaf CommRingCat :=
  (TopCat.Sheaf.pushforward _ (quotientMap n)).obj (U).sheaf

/-- The original relation structure sheaf pushed along its first projection. -/
def relationSheaf : (space n).Sheaf CommRingCat :=
  (TopCat.Sheaf.pushforward _ ((src).base ≫ quotientMap n)).obj (A).sheaf

/-- Both relation projections have the same composite to the actual orbit space. -/
theorem relation_quotientMap : (src).base ≫ quotientMap n = (tgt).base ≫ quotientMap n := by
  ext a
  exact projection_pair n a

/-- Pullback of source functions along the first relation projection. -/
def firstRestriction : sourceSheaf n ⟶ relationSheaf n :=
  ⟨(TopCat.Presheaf.pushforward _ (quotientMap n)).map (src).toPshHom.c⟩

/-- Pullback along the second projection, on the identical orbit open domains. -/
def secondRestriction : sourceSheaf n ⟶ relationSheaf n :=
  ⟨(TopCat.Presheaf.pushforward _ (quotientMap n)).map (tgt).toPshHom.c ≫
    (TopCat.Presheaf.pushforwardEq (relation_quotientMap n).symm (A).presheaf).hom⟩

/-- The actual sheaf of invariant regular functions on the orbit space. -/
def invariantSheaf : (space n).Sheaf CommRingCat :=
  equalizer (firstRestriction n) (secondRestriction n)

/-- Invariant functions included in all source regular functions. -/
def invariantInclusion : invariantSheaf n ⟶ sourceSheaf n :=
  equalizer.ι (firstRestriction n) (secondRestriction n)

instance invariantInclusion_mono : Mono (invariantInclusion n) :=
  inferInstanceAs (Mono (equalizer.ι (firstRestriction n) (secondRestriction n)))

/-- The included functions agree under the two actual relation pullbacks. -/
theorem invariantInclusion_condition :
    invariantInclusion n ≫ firstRestriction n = invariantInclusion n ≫ secondRestriction n :=
  equalizer.condition _ _

/-- Every compatible family of regular functions factors into the constructed invariant sheaf. -/
def invariantLift {F : (space n).Sheaf CommRingCat} (a : F ⟶ sourceSheaf n)
    (ha : a ≫ firstRestriction n = a ≫ secondRestriction n) : F ⟶ invariantSheaf n :=
  equalizer.lift a ha

/-- The invariant lift recovers the supplied regular functions. -/
theorem invariantLift_inclusion {F : (space n).Sheaf CommRingCat}
    (a : F ⟶ sourceSheaf n) (ha) :
    invariantLift n a ha ≫ invariantInclusion n = a := equalizer.lift_ι _ _

/-- Invariant lifts are determined by their source regular functions. -/
theorem invariantLift_unique {F : (space n).Sheaf CommRingCat}
    (a : F ⟶ sourceSheaf n) (ha) (b : F ⟶ invariantSheaf n)
    (hb : b ≫ invariantInclusion n = a) : b = invariantLift n a ha := by
  apply (cancel_mono (invariantInclusion n)).mp
  rw [hb, invariantLift_inclusion]

/-- The orbit space with its constructed sheaf of invariant commutative rings. -/
def ringedSpace : SheafedSpace CommRingCat where
  carrier := space n
  presheaf := (invariantSheaf n).obj
  IsSheaf := (invariantSheaf n).property

/-- The original source maps to the constructed ringed orbit space. -/
def toRingedSpace : (U).toSheafedSpace ⟶ ringedSpace n :=
  ⟨quotientMap n, (invariantInclusion n).hom⟩

end FLT.Mazur.CyclicCharacteristicOrbit
