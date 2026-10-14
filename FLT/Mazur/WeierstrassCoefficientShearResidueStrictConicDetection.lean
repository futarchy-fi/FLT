/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueTerminal
public import FLT.Mazur.WeierstrassModificationXConicParameterHomExt
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneConic

/-!
# Both strict terminal components detect their entire original retained conic

The two independent full affine parameters cover the conic in either scale case.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + (s + 1)) < depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "e" => data ⟨s + 1, Nat.lt_succ_of_le hs⟩
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm e (by dsimp; omega) h3 h4
local notation "g6" => nodalDepth_tangent_constant_zero hπ hm e hk h6
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "hr" => residueTangentEquation_root W
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
open WeierstrassModificationX
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "c" => algebraMap R Q (e).b6
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "Z" => conicZeroAffineIso c g6
local notation "T" => coefficientShearResidueTerminalComponent
  hπ hm data s hs hk h3 h4 h6 hc

section Positive
variable (hpos : 0 < start + s)
local notation "hscale" => nodalDepth_tangent_scale_zero (W := W) hm hpos
local notation "K" => coefficientShearRetainedConic hπ data Q r (s + 1) hs
  ⟨s, Nat.lt_succ_self s⟩ hscale hp (lin).1 (lin).2 hr

/-- The first full terminal left chart is exactly the original first conic parameter. -/
@[reassoc] theorem coefficientShearResidueTerminalComponent_first_left :
    ProjectiveLine.left Q ≫ T 0 =
      (Z).hom ≫ coefficientConicFirstParameter (U).a₁ c hu K := by
  rw [coefficientShearResidueTerminalComponent, dite_eq_left hpos, ite_eq_left rfl,
    coefficientShearRootTerminalFirstComponent_left]

/-- The opposite full terminal left chart is the entire original second conic parameter. -/
@[reassoc] theorem coefficientShearResidueTerminalComponent_second_left :
    ProjectiveLine.left Q ≫ T 1 =
      (Z).hom ≫ coefficientConicSecondParameter (U).a₁ c hu K := by
  rw [coefficientShearResidueTerminalComponent, dite_eq_left hpos,
    ite_eq_right (by decide : (1 : Fin 2) ≠ 0), coefficientShearRootTerminalSecondComponent_left]

/-- Both complete terminal components detect the entire positive-level retained conic. -/
theorem coefficientShearResidueStrictPositiveConic_hom_ext {Y : Scheme}
    (u v : coefficientShearGlued hπ data Q r (s + 1) hs ⟶ Y)
    (h₀ : T 0 ≫ u = T 0 ≫ v) (h₁ : T 1 ≫ u = T 1 ≫ v) : K ≫ u = K ≫ v := by
  apply conicParameter_hom_ext (U).a₁ c hu
  · have h := congrArg (fun f => ProjectiveLine.left Q ≫ f) h₀
    rw [coefficientShearResidueTerminalComponent_first_left_assoc _ _ _ _ _ _ _ _ _ _ hpos,
      coefficientShearResidueTerminalComponent_first_left_assoc _ _ _ _ _ _ _ _ _ _ hpos] at h
    apply (cancel_epi (Z).hom).mp
    simpa only [coefficientConicFirstParameter, Category.assoc] using h
  · have h := congrArg (fun f => ProjectiveLine.left Q ≫ f) h₁
    rw [coefficientShearResidueTerminalComponent_second_left_assoc _ _ _ _ _ _ _ _ _ _ hpos,
      coefficientShearResidueTerminalComponent_second_left_assoc _ _ _ _ _ _ _ _ _ _ hpos] at h
    apply (cancel_epi (Z).hom).mp
    simpa only [coefficientConicSecondParameter, Category.assoc] using h
end Positive

section ScaleOne
variable (hzero : start + s = 0)
local notation "hone" => show algebraMap R Q (π ^ (start + s)) = 1 from by
  rw [hzero, pow_zero, map_one]
local notation "K" => coefficientShearRetainedScaleOneConic hπ data Q r s hs 0 hs
  hone hp (lin).1 (lin).2 hr

/-- The first full scale-one terminal left chart retains the original first conic parameter. -/
@[reassoc] theorem coefficientShearResidueTerminalComponent_zero_first_left :
    ProjectiveLine.left Q ≫ T 0 =
      (Z).hom ≫ coefficientConicFirstParameter (U).a₁ c hu K := by
  rw [coefficientShearResidueTerminalComponent, dite_eq_right (by omega), ite_eq_left rfl,
    coefficientShearRootTerminalZeroFirstComponent_left]

/-- The opposite scale-one terminal left chart retains the original second conic parameter. -/
@[reassoc] theorem coefficientShearResidueTerminalComponent_zero_second_left :
    ProjectiveLine.left Q ≫ T 1 =
      (Z).hom ≫ coefficientConicSecondParameter (U).a₁ c hu K := by
  rw [coefficientShearResidueTerminalComponent, dite_eq_right (by omega),
    ite_eq_right (by decide : (1 : Fin 2) ≠ 0),
    coefficientShearRootTerminalZeroSecondComponent_left]

/-- Both complete terminal components detect the entire scale-one retained conic. -/
theorem coefficientShearResidueStrictZeroConic_hom_ext {Y : Scheme}
    (u v : coefficientShearGlued hπ data Q r (s + 1) hs ⟶ Y)
    (h₀ : T 0 ≫ u = T 0 ≫ v) (h₁ : T 1 ≫ u = T 1 ≫ v) : K ≫ u = K ≫ v := by
  apply conicParameter_hom_ext (U).a₁ c hu
  · have h := congrArg (fun f => ProjectiveLine.left Q ≫ f) h₀
    rw [coefficientShearResidueTerminalComponent_zero_first_left_assoc
      _ _ _ _ _ _ _ _ _ _ hzero,
      coefficientShearResidueTerminalComponent_zero_first_left_assoc
        _ _ _ _ _ _ _ _ _ _ hzero] at h
    apply (cancel_epi (Z).hom).mp
    simpa only [coefficientConicFirstParameter, Category.assoc] using h
  · have h := congrArg (fun f => ProjectiveLine.left Q ≫ f) h₁
    rw [coefficientShearResidueTerminalComponent_zero_second_left_assoc
      _ _ _ _ _ _ _ _ _ _ hzero,
      coefficientShearResidueTerminalComponent_zero_second_left_assoc
        _ _ _ _ _ _ _ _ _ _ hzero] at h
    apply (cancel_epi (Z).hom).mp
    simpa only [coefficientConicSecondParameter, Category.assoc] using h
end ScaleOne

end FLT.Mazur.WeierstrassDividedDepth
