/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXBaseChange
public import FLT.Mazur.PrincipalOpenTensorRange

/-!
# Principal boundary ranges in the named successive tensor algebra

Express the generic tensor localization test in the original named coordinate
algebra before substituting large retained atlas indices.
-/

@[expose] public noncomputable section
open AlgebraicGeometry
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] TensorProduct
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S]

/-- The full localization image tests the original named tensor coordinate. -/
theorem tensorBoundary_mem_range (i : Fin 3)
    (z : Spec (.of (ScalarExtension W s π b3 b4 b6 S))) :
    z ∈ Set.range (PrincipalOpenTensor.inclusion S (coord W s π b3 b4 b6 i)) ↔
      tensorCoord W s π b3 b4 b6 S i ∉ z.asIdeal := by
  exact PrincipalOpenTensor.mem_inclusion_range S (coord W s π b3 b4 b6 i) z

end FLT.Mazur.WeierstrassSuccessiveX
