/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchMap
public import FLT.Mazur.WeierstrassDividedTangentBranchResidueUnit

/-!
# Terminal smoothness of the actual specialized branch formula

A ring specialization killing the scale and the two branch ordinates sends
the actual constructed vertical derivative to a unit when the next constant
coefficient is invertible. No field or characteristic restriction is needed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassCurve
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (s b3 a2 b4' b6' u₁ u₂ v₁ v₂ : R)
  (hc : IsUnit (v₁ + W.a₁ * u₁ + b3))
  (hd : IsUnit (v₁ + v₂ + W.a₁ * u₂ + b3))
local notation "k" => tangentBranchSlope W b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd
local notation "X" => tangentBranchX W s a2 u₁ u₂ k
local notation "Y" => tangentBranchY W s b3 a2 u₁ u₂ v₁ k

/-- Specialization proves the actual branch output is vertically smooth at a terminal residue. -/
theorem tangentBranch_specialized_vertical_isUnit
    (hs : f s = 0) (h3 : f b3 = 0) (h₁ : f v₁ = 0) (h₂ : f v₂ = 0)
    (h6 : IsUnit (f b6')) : IsUnit (f (2 * Y + W.a₁ * X + b3)) := by
  have hc' : IsUnit (f v₁ + (W.map f).a₁ * f u₁ + f b3) := by
    simpa only [map_add, map_mul, map_a₁] using hc.map f
  have hd' : IsUnit (f v₁ + f v₂ + (W.map f).a₁ * f u₂ + f b3) := by
    simpa only [map_add, map_mul, map_a₁] using hd.map f
  simp only [map_add, map_mul, map_ofNat,
    tangentBranchX_map f W s b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd hc' hd',
    tangentBranchY_map f W s b3 a2 b4' b6' u₁ u₂ v₁ v₂ hc hd hc' hd']
  exact tangentBranch_residue_vertical_isUnit (W.map f) (f s) (f b3) (f a2)
    (f b4') (f b6') (f u₁) (f u₂) (f v₁) (f v₂) hc' hd' hs h3 h₁ h₂ h6

end FLT.Mazur.WeierstrassDilatation
