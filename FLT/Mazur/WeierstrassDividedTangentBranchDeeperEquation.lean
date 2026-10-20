/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchDeeperCoordinates

/-!
# The doubled-depth equation of a nonterminal branch output

Flatness preserves regularity of the scale. Cancelling its square in the
proved first divided equation yields the actual deeper equation.
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

variable (b3' b6'' : R) (h3' : b3 = s * b3') (h6'' : b6' = s * b6'')
local notation "X" => dividedTangentBranchX W s b3 b4 b6 a c a2 b4' b6'
local notation "Y" => dividedTangentBranchY W s b3 b4 b6 a c a2 b4' b6'

local notation "X₂" => dividedTangentBranchDeeperX W s b3 b4 b6 a c a2 b4' b6'
  h2 h4' h6' b3' b6'' h3' h6''
local notation "Y₂" => dividedTangentBranchDeeperY W s b3 b4 b6 a c a2 b4' b6'
  h2 h4' h6' b3' b6'' h3' h6''
variable [Module.Flat R S] (hs : IsRegular s)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

include hs h3 h4 h6 in
/-- The constructed deeper coordinates satisfy the equation at the squared scale. -/
theorem dividedTangentBranchDeeper_equation :
    Y₂ ^ 2 + (algebraMap R B W.a₁ * X₂ + algebraMap R B b3') * Y₂ =
      q ^ 2 * X₂ ^ 3 + algebraMap R B W.a₂ * X₂ ^ 2 +
        algebraMap R B b4' * X₂ + algebraMap R B b6'' := by
  have hx := dividedTangentBranchDeeperX_mul W s b3 b4 b6 a c a2 b4' b6'
    h2 h4' h6' b3' b6'' h3' h6''
  have hy := dividedTangentBranchDeeperY_mul W s b3 b4 b6 a c a2 b4' b6'
    h2 h4' h6' b3' b6'' h3' h6''
  have hb3 : b3B = q * algebraMap R B b3' := by simp only [h3', map_mul]
  have hb4 : algebraMap R B b4 = q * algebraMap R B b4' := by simp only [h4', map_mul]
  have hb6 : algebraMap R B b6 = q ^ 2 * algebraMap R B b6'' := by
    simp only [h6', h6'', map_mul]
    ring
  have h := dividedTangentBranch_equation W s b3 b4 b6 a c a2 b4' b6'
    hs h2 h3 h4 h6 h4' h6'
  dsimp only at h
  rw [← hx, ← hy, hb3, hb4, hb6] at h
  apply ((dividedTangentBranch_scale_regular W s b3 b4 b6 a c hs).pow 2).left
  linear_combination h

end FLT.Mazur.WeierstrassDilatation
