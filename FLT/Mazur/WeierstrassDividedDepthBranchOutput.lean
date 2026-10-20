/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthBranchDivisibility
public import FLT.Mazur.WeierstrassDividedTangentBranchDeeperOutput

/-!
# The nonterminal branch output in an actual available depth chart

Coefficient data at twice the input depth supplies every quotient used in
the deeper output. The normalized second coefficient supplies the slope
factor. The construction targets the actual chart, with its original scale.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k l : ℕ}
  (d : Data W π k) (e : Data W π l) (hl : l = k + k)
  (h2 : W.a₂ = 0)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "B" => DividedTangentBranchRing W s d.b3 d.b4 d.b6 a c

include hπ hl in
/-- Available doubled-depth data supplies the third branch quotient. -/
theorem branch_available_factor3 : d.b3 = s * e.b3 := by
  subst l
  exact branch_depth_factor3 hπ d e

include hπ hl in
/-- Available doubled-depth data supplies the fourth branch quotient. -/
theorem branch_available_factor4 : d.b4 = s * e.b4 := by
  subst l
  exact branch_depth_factor4 hπ d e

include hπ hl in
/-- Available doubled-depth data supplies the first constant branch quotient. -/
theorem branch_available_factor6 : d.b6 = s * (s * e.b6) := by
  subst l
  exact branch_depth_first_factor6 hπ d e

local notation "h3'" => branch_available_factor3 hπ d e hl
local notation "h4'" => branch_available_factor4 hπ d e hl
local notation "h6'" => branch_available_factor6 hπ d e hl
local notation "h2'" => branch_normalized_factor2 (π := π) (k := k) h2
local notation "X₂" => dividedTangentBranchDeeperX W s d.b3 d.b4 d.b6 a c
  0 e.b4 (s * e.b6) h2' h4' h6' e.b3 e.b6 h3' rfl
local notation "Y₂" => dividedTangentBranchDeeperY W s d.b3 d.b4 d.b6 a c
  0 e.b4 (s * e.b6) h2' h4' h6' e.b3 e.b6 h3' rfl
variable [Module.Flat R S]
local notation "hs" => isRegular_iff_ne_zero.mpr (pow_ne_zero k hπ)

/-- The branch output in the actual available deeper coordinate algebra. -/
def depthBranchOutput : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] B :=
  evaluation W (π ^ l) e.b3 e.b4 e.b6 X₂ Y₂ (by
    simpa only [hl, pow_add, map_mul, pow_two] using
      dividedTangentBranchDeeper_equation W s d.b3 d.b4 d.b6 a c
        0 e.b4 (s * e.b6) h2' h4' h6' e.b3 e.b6 h3' rfl hs
        d.factor3 d.factor4 d.factor6)

/-- The actual deeper chart has the constructed divided abscissa. -/
theorem depthBranchOutput_x :
    depthBranchOutput hπ d e hl h2 a c (x W (π ^ l) e.b3 e.b4 e.b6) = X₂ :=
  evaluation_x ..

/-- The actual deeper chart has the constructed divided ordinate. -/
theorem depthBranchOutput_y :
    depthBranchOutput hπ d e hl h2 a c (y W (π ^ l) e.b3 e.b4 e.b6) = Y₂ :=
  evaluation_y ..

/-- The entire older output is recovered by the actual depth transition. -/
theorem depthBranchOutput_transition (hkl : k ≤ l) :
    (depthBranchOutput hπ d e hl h2 a c).comp
      (depthTransition π k l hπ hkl W d.b3 d.b4 d.b6 e.b3 e.b4 e.b6
        d.factor3 d.factor4 d.factor6 e.factor3 e.factor4 e.factor6) =
      dividedTangentBranchOutput W s d.b3 d.b4 d.b6 a c 0 e.b4 (s * e.b6)
        hs h2' d.factor3 d.factor4 d.factor6 h4' h6' := by
  apply hom_ext
  · simp only [AlgHom.comp_apply, depthTransition_x, map_mul, AlgHom.commutes,
      depthBranchOutput_x, dividedTangentBranchOutput_x, hl, Nat.add_sub_cancel_left]
    exact dividedTangentBranchDeeperX_mul W s d.b3 d.b4 d.b6 a c
      0 e.b4 (s * e.b6) h2' h4' h6' e.b3 e.b6 h3' rfl
  · simp only [AlgHom.comp_apply, depthTransition_y, map_mul, AlgHom.commutes,
      depthBranchOutput_y, dividedTangentBranchOutput_y, hl, Nat.add_sub_cancel_left]
    exact dividedTangentBranchDeeperY_mul W s d.b3 d.b4 d.b6 a c
      0 e.b4 (s * e.b6) h2' h4' h6' e.b3 e.b6 h3' rfl

end FLT.Mazur.WeierstrassDividedDepth
