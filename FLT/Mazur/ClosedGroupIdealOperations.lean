/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealPullbackVanishingCriterion
public import FLT.Mazur.CartesianMonoGroup
public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# Equations for the operations on a closed group subscheme

The multiplication equation is the actual pulled ideal map on D × D. Its
vanishing constructs multiplication on the entire closed subscheme, including
its nilpotent structure. The same construction applies to unit and inverse.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj GrpObj
universe u
namespace FLT.Mazur.ClosedGroupIdeal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} (G : Over S) (I : G.left.IdealSheafData)

/-- The actual closed subscheme over the original base. -/
def carrier : Over S := Over.mk (I.subschemeι ≫ G.hom)

/-- The original closed immersion, as a morphism over the base. -/
def inclusion : carrier G I ⟶ G := Over.homMk I.subschemeι

instance inclusion_closed : IsClosedImmersion (inclusion G I).left :=
  inferInstanceAs (IsClosedImmersion I.subschemeι)

instance inclusion_mono : Mono (inclusion G I) := Over.mono_of_mono_left _

/-- Lift a morphism over the base when its pulled ideal map vanishes. -/
def lift {T : Over S} (f : T ⟶ G)
    (h : FCurve.idealModulePullbackι I f.left = 0) : T ⟶ carrier G I :=
  Over.homMk (IsClosedImmersion.lift I.subschemeι f.left (by
    simpa using (FCurve.idealModulePullbackι_eq_zero_iff I f.left).mp h)) (by
      change _ ≫ (I.subschemeι ≫ G.hom) = T.hom
      rw [IsClosedImmersion.lift_fac_assoc, Over.w])

/-- The lifted map retains the given ambient morphism. -/
@[reassoc (attr := simp)] theorem lift_inclusion {T : Over S} (f : T ⟶ G)
    (h : FCurve.idealModulePullbackι I f.left = 0) :
    lift G I f h ≫ inclusion G I = f := by
  apply Over.OverMorphism.ext
  exact IsClosedImmersion.lift_fac _ _ _

/-- Factorization in the slice category is exactly the pulled ideal equation. -/
theorem vanishing_iff_lift {T : Over S} (f : T ⟶ G) :
    FCurve.idealModulePullbackι I f.left = 0 ↔
      ∃ g : T ⟶ carrier G I, g ≫ inclusion G I = f := by
  constructor
  · intro h
    exact ⟨lift G I f h, lift_inclusion G I f h⟩
  · rintro ⟨g, rfl⟩
    apply (FCurve.idealModulePullbackι_eq_zero_iff_lift I _).mpr
    exact ⟨g.left, rfl⟩

variable [CommGrpObj G]

/-- Ambient multiplication restricted to the actual product of the divisor. -/
def productMap : carrier G I ⊗ carrier G I ⟶ G :=
  (inclusion G I ⊗ₘ inclusion G I) ≫ μ[G]

/-- The multiplication equation on the entire product, as a module-sheaf morphism. -/
def multiplicationEquation := FCurve.idealModulePullbackι I (productMap G I).left

/-- The unit equation on the original base. -/
def unitEquation := FCurve.idealModulePullbackι I (η[G]).left

/-- The inverse equation on the entire divisor. -/
def inverseEquation := FCurve.idealModulePullbackι I (inclusion G I ≫ ι[G]).left

/-- Vanishing of the product equation constructs the restricted multiplication. -/
def multiplication (h : multiplicationEquation G I = 0) :
    carrier G I ⊗ carrier G I ⟶ carrier G I := lift G I (productMap G I) h

/-- Vanishing of the unit equation constructs the restricted unit. -/
def unit (h : unitEquation G I = 0) : 𝟙_ (Over S) ⟶ carrier G I := lift G I η[G] h

/-- Vanishing of the inverse equation constructs the restricted inverse. -/
def inverse (h : inverseEquation G I = 0) : carrier G I ⟶ carrier G I :=
  lift G I (inclusion G I ≫ ι[G]) h

/-- The restricted multiplication is the actual ambient group law. -/
@[reassoc] theorem multiplication_inclusion (h : multiplicationEquation G I = 0) :
    multiplication G I h ≫ inclusion G I = (inclusion G I ⊗ₘ inclusion G I) ≫ μ[G] :=
  lift_inclusion G I _ h

/-- The restricted unit is the actual ambient identity. -/
@[reassoc] theorem unit_inclusion (h : unitEquation G I = 0) :
    unit G I h ≫ inclusion G I = η[G] := lift_inclusion G I _ h

/-- The restricted inverse is the actual ambient inverse. -/
@[reassoc] theorem inverse_inclusion (h : inverseEquation G I = 0) :
    inverse G I h ≫ inclusion G I = inclusion G I ≫ ι[G] := lift_inclusion G I _ h

end FLT.Mazur.ClosedGroupIdeal
