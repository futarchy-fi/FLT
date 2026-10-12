/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalUnitAddition

/-!
# Laurent unit points under a change of test algebra

Transport the entire scheme map, including both inverse Laurent generators.
This supplies the actual torus input when a computed action is specialized.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (p : Aˣ)

/-- The actual torus point is natural for every map of test algebras. -/
theorem laurentUnitOverPoint_natural :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (laurentUnitOverPoint (R := R) p).left =
      (laurentUnitOverPoint (R := R) (Units.map f.toMonoidHom p)).left := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  exact congrArg (fun g => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom g)))
    (LaurentUnitPoints.evalUnit_natural f p)

end FLT.Mazur.WeierstrassIntegralChart
