/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXAlgebra
public import FLT.Mazur.PrincipalOpenTensorRange

/-!
# Unit scale makes the entire initial chart an incidence boundary

The equation `t * x = s` makes both coordinates units when the scale is a unit.
This persists under every coefficient extension, including arithmetic quotients.
In particular, creation depth zero has scale one and needs no residue argument.
-/

@[expose] public noncomputable section
open AlgebraicGeometry
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- A unit scale forces the original incidence coordinate to be a unit. -/
theorem t_isUnit_of_scale_isUnit (hs : IsUnit s) : IsUnit (t W s b3 b4 b6) := by
  apply isUnit_of_mul_isUnit_left (y := x W s b3 b4 b6)
  rw [incidence]
  exact hs.map (algebraMap R _)

/-- A unit scale also forces the recovered original horizontal coordinate to be a unit. -/
theorem x_isUnit_of_scale_isUnit (hs : IsUnit s) : IsUnit (x W s b3 b4 b6) := by
  apply isUnit_of_mul_isUnit_right (x := t W s b3 b4 b6)
  rw [incidence]
  exact hs.map (algebraMap R _)

variable (S : Type u) [CommRing S] [Algebra R S]

/-- The full tensor incidence coordinate remains a unit after arbitrary coefficient extension. -/
theorem tensor_t_isUnit_of_scale_isUnit (hs : IsUnit s) :
    IsUnit ((1 : S) ⊗ₜ[R] t W s b3 b4 b6) :=
  (t_isUnit_of_scale_isUnit W s b3 b4 b6 hs).map
    (Algebra.TensorProduct.includeRight :
      Coordinate W s b3 b4 b6 →ₐ[R] S ⊗[R] Coordinate W s b3 b4 b6)

/-- Every point of the full coefficient chart lies in its original incidence boundary. -/
theorem tensor_incidence_mem_of_scale_isUnit (hs : IsUnit s)
    (p : Spec (.of (S ⊗[R] Coordinate W s b3 b4 b6))) :
    p ∈ Set.range (PrincipalOpenTensor.inclusion S (t W s b3 b4 b6)) := by
  apply (PrincipalOpenTensor.mem_inclusion_range S (t W s b3 b4 b6) p).mpr
  intro hp
  exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp
    (tensor_t_isUnit_of_scale_isUnit W s b3 b4 b6 S hs))

end FLT.Mazur.WeierstrassModificationX
