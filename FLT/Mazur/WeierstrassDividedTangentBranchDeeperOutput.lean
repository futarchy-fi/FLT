/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchDeeperEquation
public import FLT.Mazur.WeierstrassDilatationRefinement

/-!
# Construct the nonterminal branch output at doubled depth

The proved deeper equation defines an actual algebra map. Refinement recovers
the entire previous divided output, not just its original contraction.
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

local notation "out" => dividedTangentBranchOutput W s b3 b4 b6 a c a2 b4' b6'
  hs h2 h3 h4 h6 h4' h6'

/-- The next algebra map lands in the chart at twice the original depth. -/
def dividedTangentBranchDeeperOutput : Coordinate W (s * s) b3' b4' b6'' →ₐ[R] B :=
  evaluation W (s * s) b3' b4' b6'' X₂ Y₂ (by
    simpa only [map_mul, pow_two] using dividedTangentBranchDeeper_equation
      W s b3 b4 b6 a c a2 b4' b6' h2 h4' h6' b3' b6'' h3' h6'' hs h3 h4 h6)

local notation "out₂" => dividedTangentBranchDeeperOutput W s b3 b4 b6 a c a2 b4' b6'
  h2 h4' h6' b3' b6'' h3' h6'' hs h3 h4 h6

/-- The next algebra map has exactly the constructed deeper abscissa. -/
theorem dividedTangentBranchDeeperOutput_x : out₂ (x W (s * s) b3' b4' b6'') = X₂ :=
  evaluation_x ..

/-- The next algebra map has exactly the constructed deeper ordinate. -/
theorem dividedTangentBranchDeeperOutput_y : out₂ (y W (s * s) b3' b4' b6'') = Y₂ :=
  evaluation_y ..

include h6' h6'' in
/-- The original constant quotient factors through the square of the intervening scale. -/
theorem tangentBranch_deeper_factor6 : b6 = s ^ 2 * b6'' := by
  rw [h6', h6'']
  ring

local notation "h66" => tangentBranch_deeper_factor6 s b6 b6' h6' b6'' h6''

/-- The complete first divided output is retained by the next chart refinement. -/
theorem dividedTangentBranchDeeperOutput_refinement :
    (out₂).comp (refinement W s s b3 b4 b6 b3' b4' b6'' h3' h4' h66) = out := by
  apply hom_ext
  · simp only [AlgHom.comp_apply, refinement_x, map_mul, AlgHom.commutes,
      dividedTangentBranchDeeperOutput_x, dividedTangentBranchOutput_x]
    exact dividedTangentBranchDeeperX_mul W s b3 b4 b6 a c a2 b4' b6'
      h2 h4' h6' b3' b6'' h3' h6''
  · simp only [AlgHom.comp_apply, refinement_y, map_mul, AlgHom.commutes,
      dividedTangentBranchDeeperOutput_y, dividedTangentBranchOutput_y]
    exact dividedTangentBranchDeeperY_mul W s b3 b4 b6 a c a2 b4' b6'
      h2 h4' h6' b3' b6'' h3' h6''

end FLT.Mazur.WeierstrassDilatation
