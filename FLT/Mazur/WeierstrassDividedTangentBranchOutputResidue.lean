/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchOutput
public import FLT.Mazur.WeierstrassDividedTangentBranchSpecialization
public import FLT.Mazur.WeierstrassDividedVerticalSmooth

/-!
# Terminal residue smoothness for the actual branch algebra map

Identify the pullback of the divided vertical derivative with the constructed
branch formula, and prove that its terminal specializations are units.
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

variable (a2 b4' b6' : R) [Module.Flat R S] (hs : IsRegular s)
  (h2 : W.a₂ = s * a2) (h3 : W.a₃ = s * b3)
  (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (h4' : b4 = s * b4') (h6' : b6 = s * b6')
local notation "out" => dividedTangentBranchOutput W s b3 b4 b6 a c
  a2 b4' b6' hs h2 h3 h4 h6 h4' h6'

/-- The actual output pulls back the divided vertical derivative to its explicit formula. -/
theorem dividedTangentBranchOutput_vertical :
    out (verticalDerivative W s b3 b4 b6) =
      2 * dividedTangentBranchY W s b3 b4 b6 a c a2 b4' b6' +
      (W').a₁ * dividedTangentBranchX W s b3 b4 b6 a c a2 b4' b6' + b3B := by
  rw [verticalDerivative_eq]
  simp only [map_add, map_mul, map_ofNat, AlgHom.commutes, map_a₁,
    dividedTangentBranchOutput_x, dividedTangentBranchOutput_y]

/-- Every terminal specialization of the actual output has invertible vertical derivative. -/
theorem dividedTangentBranchOutput_specialized_vertical
    {K : Type*} [CommRing K] (f : B →+* K)
    (hs0 : f q = 0) (hb3 : f b3B = 0) (hv1 : f v₁ = 0) (hv2 : f v₂ = 0)
    (hb6 : IsUnit (f (algebraMap R B b6'))) :
    IsUnit (f (out (verticalDerivative W s b3 b4 b6))) := by
  rw [dividedTangentBranchOutput_vertical]
  exact tangentBranch_specialized_vertical_isUnit f W' q b3B
    (algebraMap R B a2) (algebraMap R B b4') (algebraMap R B b6') u₁ u₂ v₁ v₂
    (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).1
    (dividedTangentBranch_coordinate_units W s b3 b4 b6 a c).2 hs0 hb3 hv1 hv2 hb6

end FLT.Mazur.WeierstrassDilatation
