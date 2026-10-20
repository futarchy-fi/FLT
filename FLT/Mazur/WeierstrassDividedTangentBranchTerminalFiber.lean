/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchOutputResidue
public import FLT.Mazur.WeierstrassDividedTangentBranchSpecialFiber

/-!
# The complete terminal fiber of the strict-branch source has smooth output

Both input ordinate conditions follow from the actual source equations.
Only the coefficient specialization and terminal constant unit remain.
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

/-- The terminal fiber has invertible output derivative without assumptions on input ordinates. -/
theorem dividedTangentBranch_terminalFiber_vertical
    {K : Type*} [CommRing K] (f : B →+* K) (hs0 : f q = 0) (hb3 : f b3B = 0)
    (hb6 : IsUnit (f (algebraMap R B b6'))) :
    IsUnit (f (out (verticalDerivative W s b3 b4 b6))) := by
  have hv := dividedTangentBranch_specialFiber_ordinates W s b3 b4 b6 a c
    a2 b4' b6' h2 h4' h6' f hs0
  exact dividedTangentBranchOutput_specialized_vertical W s b3 b4 b6 a c
    a2 b4' b6' hs h2 h3 h4 h6 h4' h6' f hs0 hb3 hv.1 hv.2 hb6

/-- The whole terminal fiber is covered by the actual derivative neighborhood. -/
theorem dividedTangentBranch_terminalFiber_mem
    (p : PrimeSpectrum B) (hp : q ∈ p.asIdeal) (hp3 : b3B ∈ p.asIdeal)
    (hb6 : IsUnit b6') :
    p ∈ PrimeSpectrum.basicOpen (out (verticalDerivative W s b3 b4 b6)) := by
  let f : B →+* B ⧸ p.asIdeal := Ideal.Quotient.mk p.asIdeal
  have hv := dividedTangentBranch_terminalFiber_vertical W s b3 b4 b6 a c
    a2 b4' b6' hs h2 h3 h4 h6 h4' h6' f
    (Ideal.Quotient.eq_zero_iff_mem.mpr hp) (Ideal.Quotient.eq_zero_iff_mem.mpr hp3)
    ((hb6.map (algebraMap R B)).map f)
  change out (verticalDerivative W s b3 b4 b6) ∉ p.asIdeal
  intro he
  exact hv.ne_zero (Ideal.Quotient.eq_zero_iff_mem.mpr he)

end FLT.Mazur.WeierstrassDilatation
