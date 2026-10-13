/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroCoconeGluing
public import FLT.Mazur.WeierstrassCoefficientShearEqualityParameterCover
public import FLT.Mazur.WeierstrassCoefficientShearScaleOneEqualityParameterCover
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneConic
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroLengthTwoCoconeDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroTerminalDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroRetainedCoconeMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroAtlasCompatibility
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroAtlasCoconeMaps

import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroCoconeGluing

/-!
# The original equality component detects the complete terminal equations

Both scale cases retain their full conic and divided charts for arbitrary target schemes.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (he : 2 * (0 + (s + 1)) = depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDilatation
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "T" => coefficientShearResidueEqualityComponent
  hπ hm data s hs he h3 h4 h6next hc
local notation "d" => data ⟨s + 1, Nat.lt_succ_of_le hs⟩
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm d (Nat.le_of_eq he) h3 h4
local notation "cunit" => nodalDepth_tangent_constant_isUnit hm d he h6next
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "hr" => residueTangentEquation_root W
variable {Y : Scheme} (u v : coefficientShearGlued hπ data
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))) (s + 1) hs ⟶ Y)

/-- The whole equality component detects the entire divided chart at every chain length. -/
theorem coefficientShearResidueZeroEqualityDivided_hom_ext (h : T ≫ u = T ≫ v) :
    coefficientShearGluedChart hπ data Q r (s + 1) hs (.inl 1) ≫ u =
      coefficientShearGluedChart hπ data Q r (s + 1) hs (.inl 1) ≫ v := by
  have H := congrArg (fun f => coefficientShearEqualityDividedParameter
    data Q r s hs hp (lin).1 (lin).2 cunit hr a ha ≫ f) h
  unfold coefficientShearResidueEqualityComponent at H
  by_cases hspos : 0 < 0 + s
  · rw [dite_eq_left hspos] at H
    simpa only [coefficientShearEqualityDividedParameter_component_assoc] using H
  · rw [dite_eq_right hspos] at H
    simpa only [coefficientShearScaleOneEqualityDividedParameter_component_assoc] using H

section ScaleOne
variable (hszero : s = 0)
local notation "hone" => show algebraMap R Q (π ^ (0 + s)) = 1 from by
  rw [hszero]; simp
local notation "K₀" => coefficientShearRetainedScaleOneConic hπ data Q r s hs 0
  (by omega) hone hp (lin).1 (lin).2 hr

/-- The original length-two equality component detects the entire scale-one conic. -/
theorem coefficientShearResidueZeroEqualityScaleOneConic_hom_ext
    (h : T ≫ u = T ≫ v) : K₀ ≫ u = K₀ ≫ v := by
  have H := congrArg (fun f => coefficientShearScaleOneEqualityConicParameter
    data Q r s hs hp (lin).1 (lin).2 cunit hr a ha ≫ f) h
  rw [coefficientShearResidueEqualityComponent, dite_eq_right (by omega)] at H
  simpa only [coefficientShearScaleOneEqualityConicParameter_component_assoc] using H

end ScaleOne

variable (hspos : 0 < s)
local notation "hscale" => nodalDepth_tangent_scale_zero (W := W) hm
  (show 0 < 0 + s from by omega)
local notation "K" => coefficientShearRetainedConic hπ data Q r (s + 1) hs
  ⟨s, Nat.lt_succ_self s⟩ hscale hp (lin).1 (lin).2 hr

/-- At positive chain length the complete equality component detects its whole retained conic. -/
theorem coefficientShearResidueZeroEqualityPositiveConic_hom_ext
    (h : T ≫ u = T ≫ v) : K ≫ u = K ≫ v := by
  have H := congrArg (fun f => coefficientShearEqualityConicParameter
    data Q r s hs hscale hp (lin).1 (lin).2 cunit hr a ha ≫ f) h
  rw [coefficientShearResidueEqualityComponent, dite_eq_left (by omega)] at H
  simpa only [coefficientShearEqualityConicParameter_component_assoc] using H

end FLT.Mazur.WeierstrassDividedDepth
