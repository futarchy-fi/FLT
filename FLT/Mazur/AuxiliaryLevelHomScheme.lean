/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# The scheme of finite group markings

For an actual group scheme E over S and a finite group A, impose every
multiplication relation on the finite power E^A. The resulting equalizer
represents homomorphisms from A to sections of E. This is the equation scheme
used before removing the noninjective auxiliary markings.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj

namespace FLT.Mazur.AuxiliaryLevel

variable {S : Scheme} (E : Over S) [GrpObj E] (A : Type) [Group A] [Fintype A]

/-- All proposed values of a marking, with no relations yet. -/
abbrev markingPower : Over S := ∏ᶜ fun _ : A => E

/-- Products of the two selected values. -/
def productValues : markingPower E A ⟶ ∏ᶜ fun _ : A × A => E :=
  Pi.lift fun a => Pi.π (fun _ : A => E) a.1 * Pi.π (fun _ : A => E) a.2

/-- Values at the product of the two indices. -/
def productIndices : markingPower E A ⟶ ∏ᶜ fun _ : A × A => E :=
  Pi.lift fun a => Pi.π (fun _ : A => E) (a.1 * a.2)

/-- The actual equation scheme for group markings. -/
def homScheme : Over S := equalizer (productValues E A) (productIndices E A)

/-- The inclusion in the finite power. -/
def homInclusion : homScheme E A ⟶ markingPower E A := equalizer.ι _ _

/-- The universal marked section at an index. -/
def value (a : A) : homScheme E A ⟶ E :=
  homInclusion E A ≫ Pi.π (fun _ : A => E) a

/-- The defining equalizer equations are the group multiplication equations. -/
theorem value_mul (a b : A) : value E A (a * b) = value E A a * value E A b := by
  have h := congrArg (fun f => f ≫ Pi.π (fun _ : A × A => E) (a, b))
    (equalizer.condition (productValues E A) (productIndices E A))
  simpa only [Category.assoc, productValues, productIndices, Pi.lift_comp_π,
    MonObj.comp_mul, value, homInclusion] using h.symm

/-- The universal marking is a genuine group homomorphism. -/
def universalMarking : A →* (homScheme E A ⟶ E) :=
  MonoidHom.mk' (value E A) (value_mul E A)

/-- Any family of sections satisfying the group laws gives an actual scheme map. -/
def liftMarking {U : Over S} (f : A →* (U ⟶ E)) : U ⟶ homScheme E A :=
  equalizer.lift (Pi.lift f) (by
    apply Pi.hom_ext
    intro a
    simp only [Category.assoc, productValues, productIndices, Pi.lift_comp_π,
      MonObj.comp_mul, map_mul])

/-- Evaluation of the constructed morphism recovers the original marked sections. -/
@[reassoc (attr := simp)] theorem liftMarking_value {U : Over S}
    (f : A →* (U ⟶ E)) (a : A) : liftMarking E A f ≫ value E A a = f a := by
  simp only [liftMarking, value, homInclusion, equalizer.lift_ι_assoc, Pi.lift_comp_π]

/-- Scheme morphisms into the equation scheme are determined by their marked sections. -/
@[ext] theorem homScheme_ext {U : Over S} (f g : U ⟶ homScheme E A)
    (h : ∀ a, f ≫ value E A a = g ≫ value E A a) : f = g := by
  apply equalizer.hom_ext
  apply Pi.hom_ext
  intro a
  exact (Category.assoc _ _ _).trans ((h a).trans (Category.assoc _ _ _).symm)

/-- A point of the equation scheme is its family of sections as a homomorphism. -/
def markingOf {U : Over S} (f : U ⟶ homScheme E A) : A →* (U ⟶ E) :=
  ((yonedaGrpObj E).map f.op).hom.comp (universalMarking E A)

/-- The equation scheme represents markings on every test scheme, including nonreduced ones. -/
def markingEquiv (U : Over S) : (U ⟶ homScheme E A) ≃ (A →* (U ⟶ E)) where
  toFun := markingOf E A
  invFun := liftMarking E A
  left_inv f := by
    apply homScheme_ext
    intro a
    exact liftMarking_value E A (markingOf E A f) a
  right_inv f := by
    apply MonoidHom.ext
    intro a
    exact liftMarking_value E A f a

/-- The representation retains pullback of every marked section. -/
theorem markingOf_comp {U V : Over S} (f : U ⟶ V) (g : V ⟶ homScheme E A) (a : A) :
    markingOf E A (f ≫ g) a = f ≫ markingOf E A g a := by
  change (f ≫ g) ≫ value E A a = f ≫ g ≫ value E A a
  exact Category.assoc _ _ _

end FLT.Mazur.AuxiliaryLevel
