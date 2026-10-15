/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXLaurentNodeParameter

/-!
# The complete standard puncture lies in the full initial node neighborhood

On D(p), the opposite coordinate belongs to the original nilpotent arithmetic
ideal. Thus q+a₁ is invertible, retaining the complete initial node functions.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁) (hs : s ∈ I)
local notation "N" => NodalFiber.Coordinate s
local notation "D" => Localization.Away (NodalFiber.p s)
local notation "L" => PolynomialNodeOpen W s
local notation "ι" => algebraMap N D
local notation "J" => I.map (algebraMap R D)

include hs in
/-- The complete opposite coordinate on D(p) lies in the original arithmetic ideal. -/
theorem standardInitialPuncture_q_mem : ι (NodalFiber.q s) ∈ J := by
  apply ((J).unit_mul_mem_iff_mem
    (IsLocalization.Away.algebraMap_isUnit (S := D) (NodalFiber.p s))).mp
  rw [← map_mul, NodalFiber.relation, ← IsScalarTower.algebraMap_apply R N D]
  exact Ideal.mem_map_of_mem _ hs

include hI ha hs in
/-- The whole standard puncture lies in the original full node neighborhood D(q+a₁). -/
theorem standardInitialPuncture_denominator_unit :
    IsUnit (ι (NodalFiber.q s) + algebraMap R D W.a₁) := by
  exact (NilpotentQuadraticRoot.element_nilpotent J 
    (NilpotentPolynomialInverse.mapIdeal_nilpotent I hI (algebraMap R D))
      (standardInitialPuncture_q_mem s I hs)).isUnit_add_right_of_commute
        (ha.map (algebraMap R D)) (mul_comm _ _)

/-- Restrict all initial node functions to the entire standard puncture D(p). -/
def initialNodeStandardPuncture : L →ₐ[R] D :=
  IsLocalization.Away.liftAlgHom (NodalFiber.q s + algebraMap R N W.a₁)
    (f := IsScalarTower.toAlgHom R N D)
    (by
      change IsUnit (ι (NodalFiber.q s + algebraMap R N W.a₁))
      rw [map_add, ← IsScalarTower.algebraMap_apply R N D]
      exact standardInitialPuncture_denominator_unit W s I hI ha hs)

/-- The complete standard restriction retains every node function. -/
theorem initialNodeStandardPuncture_base (z : N) :
    initialNodeStandardPuncture W s I hI ha hs (algebraMap N L z) = ι z := by
  rw [initialNodeStandardPuncture, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

end FLT.Mazur.WeierstrassModificationX
