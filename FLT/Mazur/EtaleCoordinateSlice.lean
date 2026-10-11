/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Actual étale slices through matching coordinate points

Pulling an étale coordinate map back along a section constructs an étale
base neighborhood and an actual map to the original source. After this base
change the original source morphism has a section. Point incidence is proved
from equality of coordinates, without assuming a local-section conclusion.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EtaleCoordinateSlice
universe u
set_option backward.isDefEq.respectTransparency false
variable {U A S : Scheme.{u}} (g : U ⟶ A) (p : A ⟶ S) (t : S ⟶ A)
  (ht : t ≫ p = 𝟙 S)

/-- The slice is the actual scheme pullback of the coordinate section. -/
def space : Scheme.{u} := pullback g t

/-- The map from the slice to the original source. -/
def toSource : space g t ⟶ U := pullback.fst g t

/-- The new base neighborhood. -/
def toBase : space g t ⟶ S := pullback.snd g t

instance [Etale g] : Etale (toBase g t) := by
  unfold toBase
  exact MorphismProperty.pullback_snd g t inferInstance

include ht in
/-- Its structure map agrees with the original source structure map. -/
@[reassoc]
theorem toSource_base : toSource g t ≫ (g ≫ p) = toBase g t := by
  dsimp only [toSource, toBase]
  rw [← Category.assoc, pullback.condition, Category.assoc, ht, Category.comp_id]

/-- After the constructed étale base change, the source acquires an actual section. -/
def sectionMap : space g t ⟶ pullback (g ≫ p) (toBase g t) :=
  pullback.lift (toSource g t) (𝟙 _) (by
    rw [toSource_base g p t ht, Category.id_comp])

/-- The section is a section of the actual base-changed source projection. -/
@[reassoc]
theorem sectionMap_snd :
    sectionMap g p t ht ≫ pullback.snd (g ≫ p) (toBase g t) = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- Its source coordinate is the original slice map. -/
@[reassoc]
theorem sectionMap_fst :
    sectionMap g p t ht ≫ pullback.fst (g ≫ p) (toBase g t) = toSource g t :=
  pullback.lift_fst _ _ _

/-- Matching coordinates lift an entire test morphism, including its scheme structure. -/
def pointLift {T : Scheme.{u}} (x : T ⟶ U) (b : T ⟶ S) (h : x ≫ g = b ≫ t) :
    T ⟶ space g t := pullback.lift x b h

@[reassoc]
theorem pointLift_source {T : Scheme.{u}} (x : T ⟶ U) (b : T ⟶ S)
    (h : x ≫ g = b ≫ t) : pointLift g t x b h ≫ toSource g t = x :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem pointLift_base {T : Scheme.{u}} (x : T ⟶ U) (b : T ⟶ S)
    (h : x ≫ g = b ≫ t) : pointLift g t x b h ≫ toBase g t = b :=
  pullback.lift_snd _ _ _

/-- Incidence of coordinate points supplies a point on the constructed neighborhood. -/
theorem exists_point (x : U) (s : S) (h : g x = t s) :
    ∃ z : space g t, toSource g t z = x ∧ toBase g t z = s :=
  Scheme.Pullback.exists_preimage_pullback x s h

end FLT.Mazur.EtaleCoordinateSlice
