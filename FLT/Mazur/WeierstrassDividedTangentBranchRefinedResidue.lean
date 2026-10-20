/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchRefinedCongruence

/-!
# Unit vertical derivative at an intermediate branch residue

The refined product congruences force a unit output abscissa when the fully
removed constant is a unit. The actual branch equations provide the input
ordinate residues and the branch localization provides the tangent unit.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
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
variable (a2 b4' b6' : R)
  (h2 : W.a₂ = s * a2) (h4' : b4 = s * b4') (h6' : b6 = s * b6')
  (t : R) (hts : t ∣ s) (ht3 : t ∣ b3) (ht6 : t ∣ b6')
local notation "Xr" => dividedTangentBranchRefinedX W s b3 b4 b6 a c
  a2 b4' b6' h2 h4' h6' t hts ht3 ht6
local notation "Yr" => dividedTangentBranchRefinedY W s b3 b4 b6 a c
  a2 b4' b6' h2 h4' h6' t hts ht3 ht6
variable [Module.Flat R S] (hs : IsRegular s) (h3 : s ∣ b3)
  (w beta : R) (hw : s = t * w) (hb : b6' = t * beta)

include hs h3 hw hb in
/-- A terminal refinement has invertible vertical derivative in every nodal specialization. -/
theorem dividedTangentBranchRefined_specialized_vertical
    {T : Type*} [CommRing T] (f : B →+* T) (hf : f (algebraMap R B w) = 0)
    (hbunit : IsUnit (f (algebraMap R B beta)))
    (c3 : R) (hc3 : f (algebraMap R B c3) = 0) :
    IsUnit (f (2 * Yr + algebraMap R B W.a₁ * Xr + algebraMap R B c3)) := by
  have hs0 : f (algebraMap R B s) = 0 := by
    simp only [hw, map_mul, hf, mul_zero]
  have h30 : f (algebraMap R B b3) = 0 := by
    obtain ⟨z, hz⟩ := h3
    simp only [hz, map_mul, hs0, zero_mul]
  have hv := dividedTangentBranch_specialFiber_ordinates W s b3 b4 b6 a c
    a2 b4' b6' h2 h4' h6' f hs0
  have hu := ((dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).1).map f
  simp only [map_add, map_mul, WeierstrassCurve.map_a₁, hv.1, h30,
    zero_add, add_zero] at hu
  have ha : IsUnit (f (algebraMap R B W.a₁)) := isUnit_of_mul_isUnit_left hu
  have hp := dividedTangentBranchRefined_specialized_products W s b3 b4 b6 a c
    a2 b4' b6' h2 h4' h6' t hts ht3 ht6 hs h3 w beta hw hb f hf
  have hx : IsUnit (f Xr) := isUnit_of_mul_isUnit_right (hp.1.symm ▸ hbunit.neg)
  have he : f (2 * Yr + algebraMap R B W.a₁ * Xr + algebraMap R B c3) =
      -(f (algebraMap R B W.a₁) * f Xr) := by
    simp only [map_add, map_mul, map_ofNat, hc3]
    linear_combination 2 * hp.2
  rw [he]
  exact (ha.mul hx).neg

end FLT.Mazur.WeierstrassDilatation
