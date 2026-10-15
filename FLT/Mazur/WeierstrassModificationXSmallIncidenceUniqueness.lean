/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXLaurentNodeParameter

/-!
# Uniqueness of full small-branch evaluations at invertible incidence

The original equation and small residue label determine the entire slope
once the original incidence is fixed and invertible.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁) (h3 : b3 ∈ I)
  (f g : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "J" => I.map (algebraMap R S)
local notation "t₀" => t W s b3 b4 b6
local notation "v₀" => v W s b3 b4 b6

include hI ha h3 in
/-- The full original small branch is determined by its invertible incidence coordinate. -/
theorem smallIncidence_hom_ext (ht : f t₀ = g t₀) (hu : IsUnit (f t₀))
    (hf : f v₀ ∈ J) (hg : g v₀ ∈ J) : f = g := by
  have hJ := NilpotentPolynomialInverse.mapIdeal_nilpotent I hI (algebraMap R S)
  have hnil : algebraMap R S b3 * f t₀ ∈ J :=
    (J).mul_mem_right _ (Ideal.mem_map_of_mem _ h3)
  have hunit : IsUnit (algebraMap R S W.a₁ + algebraMap R S b3 * f t₀) :=
    (NilpotentQuadraticRoot.element_nilpotent J hJ hnil).isUnit_add_left_of_commute
      (ha.map (algebraMap R S)) (mul_comm _ _)
  apply hom_ext W s b3 b4 b6 f g ht
  apply NilpotentQuadraticRoot.root_unique J hJ
    (algebraMap R S W.a₁ + algebraMap R S b3 * f t₀)
    (f v₀ ^ 2 + (algebraMap R S W.a₁ + algebraMap R S b3 * f t₀) * f v₀)
    hunit hf hg rfl
  apply hu.mul_left_cancel
  have hfirst := congrArg f (incidence W s b3 b4 b6)
  have hsecond := congrArg g (incidence W s b3 b4 b6)
  simp only [x, map_mul, map_sub, map_add, map_pow, AlgHom.commutes] at hfirst hsecond
  rw [← ht] at hsecond
  linear_combination hsecond - hfirst

end FLT.Mazur.WeierstrassModificationX
