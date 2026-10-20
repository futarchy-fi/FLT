/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchOutputResidue

/-!
# Terminal strict-branch primes are covered by the smooth output neighborhood

The residue calculation is applied to the quotient by each actual source
prime. This proves topological coverage by the constructed principal open,
including points above an originally singular output.
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

/-- Every terminal strict-branch prime lies in the explicit output derivative open. -/
theorem dividedTangentBranchOutput_terminal_mem
    (p : PrimeSpectrum B) (hp : q ∈ p.asIdeal) (hp3 : b3B ∈ p.asIdeal)
    (hp1 : v₁ ∈ p.asIdeal) (hp2 : v₂ ∈ p.asIdeal) (hb6 : IsUnit b6') :
    p ∈ PrimeSpectrum.basicOpen (out (verticalDerivative W s b3 b4 b6)) := by
  let f : B →+* B ⧸ p.asIdeal := Ideal.Quotient.mk p.asIdeal
  have hv := dividedTangentBranchOutput_specialized_vertical W s b3 b4 b6 a c
    a2 b4' b6' hs h2 h3 h4 h6 h4' h6' f
    (Ideal.Quotient.eq_zero_iff_mem.mpr hp) (Ideal.Quotient.eq_zero_iff_mem.mpr hp3)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hp1) (Ideal.Quotient.eq_zero_iff_mem.mpr hp2)
    ((hb6.map (algebraMap R B)).map f)
  change out (verticalDerivative W s b3 b4 b6) ∉ p.asIdeal
  intro he
  exact hv.ne_zero (Ideal.Quotient.eq_zero_iff_mem.mpr he)

/-- Terminal strict-branch points are actually reached by the derivative localization. -/
theorem dividedTangentBranchOutput_terminal_range
    (p : PrimeSpectrum B) (hp : q ∈ p.asIdeal) (hp3 : b3B ∈ p.asIdeal)
    (hp1 : v₁ ∈ p.asIdeal) (hp2 : v₂ ∈ p.asIdeal) (hb6 : IsUnit b6') :
    p ∈ Set.range (PrincipalAffineRefinement.inclusion
      (out (verticalDerivative W s b3 b4 b6))) := by
  rw [PrincipalAffineRefinement.range_inclusion]
  exact dividedTangentBranchOutput_terminal_mem W s b3 b4 b6 a c
    a2 b4' b6' hs h2 h3 h4 h6 h4' h6' p hp hp3 hp1 hp2 hb6

end FLT.Mazur.WeierstrassDilatation
