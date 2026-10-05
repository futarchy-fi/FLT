/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemePicardPullback
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Relative Picard classes modulo line bundles from the base

For a scheme morphism, the relative presheaf value is the cokernel of base
pullback. Commuting squares give its comparison maps. No sheafification or
representability is asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.SchemePicard

variable {X S Y T : Scheme.{u}}

/-- Line-bundle classes modulo tensoring with pullbacks from the base. -/
abbrev RelativePic (f : X ⟶ S) := Pic X ⧸ (pullback f).range

/-- The canonical map to relative Picard classes. -/
def relativeClass (f : X ⟶ S) : Pic X →* RelativePic f :=
  QuotientGroup.mk' (pullback f).range

/-- Every relative class has a representative on the total space. -/
theorem relativeClass_surjective (f : X ⟶ S) : Function.Surjective (relativeClass f) :=
  QuotientGroup.mk'_surjective _

/-- A relative class is trivial precisely when it comes from the base. -/
theorem relativeClass_eq_one_iff (f : X ⟶ S) (a : Pic X) :
    relativeClass f a = 1 ↔ ∃ b : Pic S, pullback f b = a :=
  QuotientGroup.eq_one_iff a

/-- Equality in the relative group is exactly a base twist of the difference. -/
theorem relativeClass_eq_iff (f : X ⟶ S) (a b : Pic X) :
    relativeClass f a = relativeClass f b ↔ ∃ c : Pic S, pullback f c = a⁻¹ * b :=
  QuotientGroup.eq

/-- Pullback from the base vanishes in the relative group. -/
@[simp]
theorem relativeClass_pullback (f : X ⟶ S) (b : Pic S) :
    relativeClass f (pullback f b) = 1 :=
  (relativeClass_eq_one_iff f _).mpr ⟨b, rfl⟩

/-- Tensoring by a base line bundle does not change a relative class. -/
@[simp]
theorem relativeClass_base_twist (f : X ⟶ S) (a : Pic X) (b : Pic S) :
    relativeClass f (a * pullback f b) = relativeClass f a := by
  rw [map_mul, relativeClass_pullback, mul_one]

/-- A commuting square induces pullback on relative Picard classes. -/
def relativeMap (f : X ⟶ S) (g : Y ⟶ T) (i : X ⟶ Y) (j : S ⟶ T)
    (h : f ≫ j = i ≫ g) : RelativePic g →* RelativePic f :=
  QuotientGroup.map _ _ (pullback i) (by
    rintro a ⟨b, rfl⟩
    exact ⟨pullback j b, pullback_square f g i j h b⟩)

/-- The relative comparison pulls back the actual representing line bundle. -/
@[simp]
theorem relativeMap_class (f : X ⟶ S) (g : Y ⟶ T) (i : X ⟶ Y) (j : S ⟶ T)
    (h : f ≫ j = i ≫ g) (a : Pic Y) :
    relativeMap f g i j h (relativeClass g a) = relativeClass f (pullback i a) := rfl

/-- The identity square induces the identity map. -/
theorem relativeMap_id (f : X ⟶ S) (h : f ≫ 𝟙 S = 𝟙 X ≫ f)
    (a : RelativePic f) : relativeMap f f (𝟙 X) (𝟙 S) h a = a := by
  obtain ⟨a, rfl⟩ := relativeClass_surjective f a
  rw [relativeMap_class, pullback_id]

/-- Relative pullbacks compose around pasted commuting squares. -/
theorem relativeMap_comp {Z U : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ T) (k : Z ⟶ U)
    (i : X ⟶ Y) (j : S ⟶ T) (i' : Y ⟶ Z) (j' : T ⟶ U)
    (h : f ≫ j = i ≫ g) (h' : g ≫ j' = i' ≫ k)
    (hh : f ≫ (j ≫ j') = (i ≫ i') ≫ k) (a : RelativePic k) :
    relativeMap f k (i ≫ i') (j ≫ j') hh a =
      relativeMap f g i j h (relativeMap g k i' j' h' a) := by
  obtain ⟨a, rfl⟩ := relativeClass_surjective k a
  simp only [relativeMap_class, pullback_comp]

end FLT.Mazur.SchemePicard
