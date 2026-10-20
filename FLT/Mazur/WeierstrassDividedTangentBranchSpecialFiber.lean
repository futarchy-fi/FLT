/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchOutput

/-!
# The actual strict-branch source forces the special-fiber input ordinates

The first branch inverse divides the first ordinate by the scale. After
specialization, the tangent denominator is the second complementary branch
factor, so the second equation forces its ordinate to vanish as well.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassCurve
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
local notation "B" => DividedTangentBranchRing W s b3 b4 b6 a c
local notation "j" => IsScalarTower.toAlgHom R S B
local notation "u₁" => ((j).comp a) (x W s b3 b4 b6)
local notation "u₂" => ((j).comp c) (x W s b3 b4 b6)
local notation "v₁" => ((j).comp a) (y W s b3 b4 b6)
local notation "v₂" => ((j).comp c) (y W s b3 b4 b6)
local notation "q" => algebraMap R B s
local notation "W'" => W.map (algebraMap R B)
local notation "b3B" => algebraMap R B b3

variable (a2 b4' b6' : R)
  (h2 : W.a₂ = s * a2) (h4' : b4 = s * b4') (h6' : b6 = s * b6')

include h2 h4' h6' in
/-- Both input ordinates vanish on the special fiber of the actual strict-branch source. -/
theorem dividedTangentBranch_specialFiber_ordinates
    {K : Type*} [CommRing K] (f : B →+* K) (hs0 : f q = 0) :
    f v₁ = 0 ∧ f v₂ = 0 := by
  have hc := (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).1
  have hd := (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).2
  have h2B : (W').a₂ = q * algebraMap R B a2 := by simp only [map_a₂, h2, map_mul]
  have h4B : algebraMap R B b4 = q * algebraMap R B b4' := by simp only [h4', map_mul]
  have h6B : algebraMap R B b6 = q * algebraMap R B b6' := by simp only [h6', map_mul]
  have ht := tangentBranchOrdinate_mul W' q b3B (algebraMap R B b4)
    (algebraMap R B b6) (algebraMap R B a2) (algebraMap R B b4') (algebraMap R B b6')
    u₁ v₁ hc h2B h4B h6B (equation_map W s b3 b4 b6 ((j).comp a))
  have hv1 : f v₁ = 0 := by
    have h := congrArg f ht
    simpa only [map_mul, hs0, zero_mul] using h.symm
  refine ⟨hv1, ?_⟩
  have hd' : IsUnit (f v₂ + f (W').a₁ * f u₂ + f b3B) := by
    simpa only [map_add, map_mul, hv1, zero_add] using hd.map f
  have h2map : algebraMap R B W.a₂ = q * algebraMap R B a2 := h2B
  have he := congrArg f (equation_map W s b3 b4 b6 ((j).comp c))
  have hz : f v₂ * (f v₂ + f (W').a₁ * f u₂ + f b3B) = 0 := by
    simp only [h2map, h4B, h6B, map_add, map_mul, map_pow, hs0,
      zero_mul, add_zero] at he
    simp only [map_a₁]
    linear_combination he
  apply hd'.mul_left_inj.mp
  simpa only [zero_mul] using hz

end FLT.Mazur.WeierstrassDilatation
