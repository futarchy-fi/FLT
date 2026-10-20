/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalBranchRefinementDepth
public import FLT.Mazur.WeierstrassDividedTangentBranchRefinedOutput

/-!
# Actual intermediate-depth outputs for nonterminal nodal branches

Exact node depth supplies the intermediate divisibility conditions. The
constructed algebra map targets any chosen datum at that depth and its
transition recovers the entire first nodal branch output.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {m k r : ℕ}
  (D : SplitNodeDepth W π m) (d : Data W π k) (hdepth : 3 * k ≤ m)
  (hrk : r ≤ k) (hrm : r ≤ m - 3 * k) (e : Data W π (k + r))
  (a2 : R) (h2 : W.a₂ = π ^ k * a2)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "t" => π ^ r
local notation "B" => DividedTangentBranchRing W s d.b3 d.b4 d.b6 a c
local notation "hπ" => D.uniformizer_ne_zero
local notation "b4'" => nodalBranchFourth D d hdepth
local notation "b6'" => nodalBranchConstant D d hdepth
local notation "h4'" => nodalBranchFourth_factor D d hdepth
local notation "h6'" => nodalBranchConstant_factor D d hdepth
local notation "hts" => pow_dvd_pow π hrk
local notation "ht3" => nodalBranchRefinement_third_dvd D d hdepth hrk
local notation "ht6" => nodalBranchRefinement_constant_dvd D d hdepth hrm

include D in
/-- The third target coefficient has exactly the intervening scale factor. -/
theorem nodalRefinedBranch_factor3 : d.b3 = t * e.b3 := by
  simpa using depth_coefficient_factor π k (k + r) hπ (by omega) d.factor3 e.factor3

include D in
/-- The fourth target coefficient has exactly the intervening scale factor. -/
theorem nodalRefinedBranch_factor4 : d.b4 = t * e.b4 := by
  simpa using depth_coefficient_factor π k (k + r) hπ (by omega) d.factor4 e.factor4

include D in
/-- The constant target coefficient has the square of the intervening scale factor. -/
theorem nodalRefinedBranch_factor6 : d.b6 = t ^ 2 * e.b6 := by
  simpa using depth_constant_factor π k (k + r) hπ (by omega) d.factor6 e.factor6

local notation "hc3" => nodalRefinedBranch_factor3 D d e
local notation "hc4" => nodalRefinedBranch_factor4 D d e
local notation "hc6" => nodalRefinedBranch_factor6 D d e
local notation "X₂" => dividedTangentBranchRefinedX W s d.b3 d.b4 d.b6 a c
  a2 b4' b6' h2 h4' h6' t hts ht3 ht6
local notation "Y₂" => dividedTangentBranchRefinedY W s d.b3 d.b4 d.b6 a c
  a2 b4' b6' h2 h4' h6' t hts ht3 ht6
variable [Module.Flat R S]
local notation "hs" => isRegular_iff_ne_zero.mpr (pow_ne_zero k hπ)

/-- The actual output in the chosen intermediate-depth coordinate algebra. -/
def nodalRefinedBranchOutput : Coordinate W (π ^ (k + r)) e.b3 e.b4 e.b6 →ₐ[R] B :=
  evaluation W (π ^ (k + r)) e.b3 e.b4 e.b6 X₂ Y₂ (by
    simpa only [pow_add, map_mul] using
      dividedTangentBranchRefined_equation W s d.b3 d.b4 d.b6 a c a2 b4' b6'
        h2 h4' h6' t hts ht3 ht6 e.b3 e.b4 e.b6 hc3 hc4 hc6 hs
        d.factor3 d.factor4 d.factor6)

local notation "out" => nodalRefinedBranchOutput D d hdepth hrk hrm e a2 h2 a c

/-- The intermediate output has the constructed divided abscissa. -/
theorem nodalRefinedBranchOutput_x : out (x W (π ^ (k + r)) e.b3 e.b4 e.b6) = X₂ :=
  evaluation_x ..

/-- The intermediate output has the constructed divided ordinate. -/
theorem nodalRefinedBranchOutput_y : out (y W (π ^ (k + r)) e.b3 e.b4 e.b6) = Y₂ :=
  evaluation_y ..

/-- The intermediate chart transition retains the entire first branch output. -/
theorem nodalRefinedBranchOutput_transition :
    (out).comp (depthTransition π k (k + r) hπ (by omega) W
      d.b3 d.b4 d.b6 e.b3 e.b4 e.b6 d.factor3 d.factor4 d.factor6
      e.factor3 e.factor4 e.factor6) =
      dividedTangentBranchOutput W s d.b3 d.b4 d.b6 a c a2 b4' b6'
        hs h2 d.factor3 d.factor4 d.factor6 h4' h6' := by
  apply hom_ext
  · simp only [AlgHom.comp_apply, depthTransition_x, map_mul, AlgHom.commutes,
      nodalRefinedBranchOutput_x, dividedTangentBranchOutput_x, Nat.add_sub_cancel_left]
    exact dividedTangentBranchRefinedX_mul W s d.b3 d.b4 d.b6 a c
      a2 b4' b6' h2 h4' h6' t hts ht3 ht6
  · simp only [AlgHom.comp_apply, depthTransition_y, map_mul, AlgHom.commutes,
      nodalRefinedBranchOutput_y, dividedTangentBranchOutput_y, Nat.add_sub_cancel_left]
    exact dividedTangentBranchRefinedY_mul W s d.b3 d.b4 d.b6 a c
      a2 b4' b6' h2 h4' h6' t hts ht3 ht6

end FLT.Mazur.WeierstrassDividedDepth
