/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralSeparated
public import FLT.Mazur.WeierstrassIntegralTripleFlat
public import FLT.Mazur.WeierstrassIntegralZeroSection
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.Topology.Maps.OpenQuotient

/-!
# Faithfully flat finite presentation of the integral cubic

The explicit zero section proves surjectivity. Together with the previously
proved flatness and finite presentation this makes the structure morphism an
open quotient map, and the same conclusion holds after every base change.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The infinity section meets every fiber, including fibers of singular cubics. -/
instance integralCurveStructure_surjective : Surjective (integralCurveStructure W) := by
  constructor
  intro x
  refine ⟨integralCurveZero W x, ?_⟩
  exact congrArg (fun f => f x) (integralCurveZero_structure W)

/-- Flatness and local finite presentation make the structure morphism universally open. -/
instance integralCurveStructure_universallyOpen : UniversallyOpen (integralCurveStructure W) :=
  UniversallyOpen.of_flat _

/-- The coefficient spectrum has exactly the quotient topology induced by the cubic. -/
theorem integralCurveStructure_openQuotient : IsOpenQuotientMap (integralCurveStructure W) :=
  ⟨(integralCurveStructure W).surjective, (integralCurveStructure W).continuous,
    (integralCurveStructure W).isOpenMap⟩

variable {S : Scheme.{u}} (f : S ⟶ Spec (.of R))

/-- The zero section specializes to an actual section after arbitrary scheme base change. -/
def integralCurveBaseChangeZero : S ⟶ pullback (integralCurveStructure W) f :=
  pullback.lift (f ≫ integralCurveZero W) (𝟙 S)
    (by rw [Category.assoc, integralCurveZero_structure, Category.comp_id, Category.id_comp])

/-- The base-changed infinity point is a section of the base-changed structure map. -/
@[reassoc] theorem integralCurveBaseChangeZero_structure :
    integralCurveBaseChangeZero W f ≫ pullback.snd (integralCurveStructure W) f = 𝟙 S :=
  pullback.lift_snd _ _ _

/-- Every base change is still an open quotient, not just a surjection on field points. -/
theorem integralCurveBaseChange_openQuotient :
    IsOpenQuotientMap (pullback.snd (integralCurveStructure W) f) :=
  ⟨(pullback.snd (integralCurveStructure W) f).surjective,
    (pullback.snd (integralCurveStructure W) f).continuous,
    (pullback.snd (integralCurveStructure W) f).isOpenMap⟩

end FLT.Mazur.WeierstrassIntegralChart
