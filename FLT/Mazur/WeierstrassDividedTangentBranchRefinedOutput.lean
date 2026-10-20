/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentBranchRefinedCoordinates
public import FLT.Mazur.WeierstrassDilatationRefinement

/-!
# The intermediate-scale equation and actual strict-branch output

Flatness preserves regularity of the scale. Cancelling its square in the
proved first divided equation yields the actual refined equation.
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

variable (t : R) (hts : t ∣ s) (ht3 : t ∣ b3) (ht6 : t ∣ b6')
  (c3 c4 c6 : R) (hc3 : b3 = t * c3) (hc4 : b4 = t * c4)
  (hc6 : b6 = t ^ 2 * c6)
local notation "q'" => algebraMap R B t
local notation "X" => dividedTangentBranchX W s b3 b4 b6 a c a2 b4' b6'
local notation "Y" => dividedTangentBranchY W s b3 b4 b6 a c a2 b4' b6'

local notation "X₂" => dividedTangentBranchRefinedX W s b3 b4 b6 a c a2 b4' b6'
  h2 h4' h6' t hts ht3 ht6
local notation "Y₂" => dividedTangentBranchRefinedY W s b3 b4 b6 a c a2 b4' b6'
  h2 h4' h6' t hts ht3 ht6
variable [Module.Flat R S] (hs : IsRegular s)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

include hs h3 h4 h6 hc3 hc4 hc6 in
/-- The constructed refined coordinates satisfy the equation at the intermediate scale. -/
theorem dividedTangentBranchRefined_equation :
    Y₂ ^ 2 + (algebraMap R B W.a₁ * X₂ + algebraMap R B c3) * Y₂ =
      (q * q') * X₂ ^ 3 + algebraMap R B W.a₂ * X₂ ^ 2 +
        algebraMap R B c4 * X₂ + algebraMap R B c6 := by
  have hx := dividedTangentBranchRefinedX_mul W s b3 b4 b6 a c a2 b4' b6'
    h2 h4' h6' t hts ht3 ht6
  have hy := dividedTangentBranchRefinedY_mul W s b3 b4 b6 a c a2 b4' b6'
    h2 h4' h6' t hts ht3 ht6
  have hb3 : b3B = q' * algebraMap R B c3 := by simp only [hc3, map_mul]
  have hb4 : algebraMap R B b4 = q' * algebraMap R B c4 := by
    simp only [hc4, map_mul]
  have hb6 : algebraMap R B b6 = q' ^ 2 * algebraMap R B c6 := by
    simp only [hc6, map_mul, map_pow]
  have h := dividedTangentBranch_equation W s b3 b4 b6 a c a2 b4' b6'
    hs h2 h3 h4 h6 h4' h6'
  dsimp only at h
  rw [← hx, ← hy, hb3, hb4, hb6] at h
  have ht : IsRegular t := by
    obtain ⟨w, hw⟩ := hts
    rw [hw] at hs
    exact hs.of_mul_left
  have htB : IsRegular q' := WeierstrassIntegralChart.flatRingHom_isRegular _
    (RingHom.flat_algebraMap_iff.mpr inferInstance) ht
  apply (htB.pow 2).left
  linear_combination h

/-- Construct the output in the actual chart at the intermediate scale. -/
def dividedTangentBranchRefinedOutput : Coordinate W (s * t) c3 c4 c6 →ₐ[R] B :=
  evaluation W (s * t) c3 c4 c6 X₂ Y₂ (by
    simpa only [map_mul] using dividedTangentBranchRefined_equation
      W s b3 b4 b6 a c a2 b4' b6' h2 h4' h6' t hts ht3 ht6
      c3 c4 c6 hc3 hc4 hc6 hs h3 h4 h6)

local notation "out" => dividedTangentBranchRefinedOutput W s b3 b4 b6 a c a2 b4' b6'
  h2 h4' h6' t hts ht3 ht6 c3 c4 c6 hc3 hc4 hc6 hs h3 h4 h6

/-- The refined output has the constructed abscissa. -/
theorem dividedTangentBranchRefinedOutput_x : out (x W (s * t) c3 c4 c6) = X₂ :=
  evaluation_x ..

/-- The refined output has the constructed ordinate. -/
theorem dividedTangentBranchRefinedOutput_y : out (y W (s * t) c3 c4 c6) = Y₂ :=
  evaluation_y ..

/-- Refinement recovers the complete first output on the entire branch source. -/
theorem dividedTangentBranchRefinedOutput_refinement :
    (out).comp (refinement W s t b3 b4 b6 c3 c4 c6 hc3 hc4 hc6) =
      dividedTangentBranchOutput W s b3 b4 b6 a c a2 b4' b6'
        hs h2 h3 h4 h6 h4' h6' := by
  apply hom_ext
  · simp only [AlgHom.comp_apply, refinement_x, map_mul, AlgHom.commutes,
      dividedTangentBranchRefinedOutput_x, dividedTangentBranchOutput_x]
    exact dividedTangentBranchRefinedX_mul W s b3 b4 b6 a c a2 b4' b6'
      h2 h4' h6' t hts ht3 ht6
  · simp only [AlgHom.comp_apply, refinement_y, map_mul, AlgHom.commutes,
      dividedTangentBranchRefinedOutput_y, dividedTangentBranchOutput_y]
    exact dividedTangentBranchRefinedY_mul W s b3 b4 b6 a c a2 b4' b6'
      h2 h4' h6' t hts ht3 ht6

end FLT.Mazur.WeierstrassDilatation
