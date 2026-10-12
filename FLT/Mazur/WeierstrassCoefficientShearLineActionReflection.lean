/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearTorusReflection
public import FLT.Mazur.WeierstrassCoefficientShearRetainedLineRootChange
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedLineRootChange

/-!
# Actual retained line actions under tangent-root reflection

Both full affine-line embeddings are compared independently through their
original tensor functions. The acting torus is unrestricted and its parameter is inverted.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type) [CommRing S] [Algebra R S] (r : S) (j k : ℕ)
  (hj : j ≤ n) (hk : k + 1 ≤ j)
  (a : Sˣ) (ha : (a : S) = (W.map (algebraMap R S)).a₁ + 2 * r)
  (hr : r ^ 2 + (W.map (algebraMap R S)).a₁ * r - (W.map (algebraMap R S)).a₂ = 0)
  (h3 : (W.map (algebraMap R S)).a₃ = 0)
  (h4 : (W.map (algebraMap R S)).a₄ = 0)
  (h6 : (W.map (algebraMap R S)).a₆ = 0)
  (hscale : algebraMap R S (π ^ (start + k)) = 0) (hp : algebraMap R S π = 0)
  (hd3 : algebraMap R S (data ⟨k + 1, by omega⟩).b3 = 0)
  (hd4 : algebraMap R S (data ⟨k + 1, by omega⟩).b4 = 0)
local notation "V" => W.map (algebraMap R S)
local notation "s" => (-(V).a₁ - r)
local notation "hb" => rootShearOpposite_tangent V r a ha
local notation "hs" => rootShearOpposite_root V r hr
local notation "Ur" => rootShearCurve V r
local notation "Us" => rootShearCurve V s
local notation "C" => coefficientShearRootChange hπ data S r s j hj
local notation "ι" => Spec.map (CommRingCat.ofHom
  (LaurentPolynomial.invert (R := S)).toRingHom)
local notation "Lr" => coefficientShearRetainedLine hπ data S r j hj ⟨k, by omega⟩
  hscale hp hd3 hd4 hr
local notation "Ls" => coefficientShearRetainedLine hπ data S s j hj ⟨k, by omega⟩
  hscale hp hd3 hd4 hs
local notation "g" => Over.hom (MultiplicativeGroupScheme.gm S)
local notation "gr" => coefficientShearGluedStructure hπ data S r j hj
local notation "gs" => coefficientShearGluedStructure hπ data S s j hj
local notation "Ar" => coefficientShearTorusAction hπ data S r j hj a ha hr h3 h4 h6
local notation "As" => coefficientShearTorusAction hπ data S s j hj (-a) hb hs h3 h4 h6
variable {T : Scheme} (p : T ⟶ (MultiplicativeGroupScheme.gm S).left)
  (z : T ⟶ Spec (.of (Polynomial S)))

include hk in
/-- Reflection exchanges the independently constructed line embeddings for every test scheme. -/
theorem coefficientShearLineReflection_first :
    (z ≫ Lr 0 (middle_first_root Ur)) ≫ (C).hom =
      z ≫ Ls (-(Us).a₁) (middle_second_root Us) := by
  rw [Category.assoc, coefficientShearRootChange_retainedFirst hπ data S r s j k hj hk]
  change r + (-algebraMap R S W.a₁ - r) = -algebraMap R S W.a₁
  ring

include hk ha h3 h4 h6 in
/-- The reflected whole first line has the actual inverted-parameter action domain. -/
theorem coefficientShearLineReflection_firstCondition
    (hpz : p ≫ g = (z ≫ Lr 0 (middle_first_root Ur)) ≫ gr) :
    (p ≫ ι) ≫ g = (z ≫ Ls (-(Us).a₁) (middle_second_root Us)) ≫ gs := by
  have H := coefficientShearTorusReflection_condition hπ data S r j hj a ha hr h3 h4 h6
    p (z ≫ Lr 0 (middle_first_root Ur)) hpz
  rw [coefficientShearLineReflection_first hπ data S r j k hj hk] at H
  exact H

/-- The full first-line action becomes the actual opposite-line action at the inverse parameter. -/
theorem coefficientShearLineReflection_firstAction
    (hpz : p ≫ g = (z ≫ Lr 0 (middle_first_root Ur)) ≫ gr) :
    pullback.lift (p ≫ ι) (z ≫ Ls (-(Us).a₁) (middle_second_root Us))
        (coefficientShearLineReflection_firstCondition hπ data S r j k hj hk a ha hr h3 h4 h6
          hscale hp hd3 hd4 p z hpz) ≫ As =
      pullback.lift p (z ≫ Lr 0 (middle_first_root Ur)) hpz ≫ Ar ≫ (C).hom := by
  have H := coefficientShearTorusReflection_actionPair hπ data S r j hj a ha hr h3 h4 h6
    p (z ≫ Lr 0 (middle_first_root Ur)) hpz
  refine Eq.trans ?_ H
  apply congrArg (fun f => f ≫ As)
  apply pullback.hom_ext
  · simp only [pullback.lift_fst]
  · simp only [pullback.lift_snd]
    exact (coefficientShearLineReflection_first hπ data S r j k hj hk hr
      hscale hp hd3 hd4 z).symm

include hk in
/-- Reflection exchanges the independently constructed line embeddings for every test scheme. -/
theorem coefficientShearLineReflection_second :
    (z ≫ Lr (-(Ur).a₁) (middle_second_root Ur)) ≫ (C).hom =
      z ≫ Ls 0 (middle_first_root Us) := by
  rw [Category.assoc, coefficientShearRootChange_retainedSecond hπ data S r s j k hj hk]
  change r + (-algebraMap R S W.a₁ - r) = -algebraMap R S W.a₁
  ring

include hk ha h3 h4 h6 in
/-- The reflected whole opposite line has the actual inverted-parameter action domain. -/
theorem coefficientShearLineReflection_secondCondition
    (hpz : p ≫ g = (z ≫ Lr (-(Ur).a₁) (middle_second_root Ur)) ≫ gr) :
    (p ≫ ι) ≫ g = (z ≫ Ls 0 (middle_first_root Us)) ≫ gs := by
  have H := coefficientShearTorusReflection_condition hπ data S r j hj a ha hr h3 h4 h6
    p (z ≫ Lr (-(Ur).a₁) (middle_second_root Ur)) hpz
  rw [coefficientShearLineReflection_second hπ data S r j k hj hk] at H
  exact H

/-- The full opposite-line action becomes the actual first-line action at the inverse parameter. -/
theorem coefficientShearLineReflection_secondAction
    (hpz : p ≫ g = (z ≫ Lr (-(Ur).a₁) (middle_second_root Ur)) ≫ gr) :
    pullback.lift (p ≫ ι) (z ≫ Ls 0 (middle_first_root Us))
        (coefficientShearLineReflection_secondCondition hπ data S r j k hj hk a ha hr h3 h4 h6
          hscale hp hd3 hd4 p z hpz) ≫ As =
      pullback.lift p (z ≫ Lr (-(Ur).a₁) (middle_second_root Ur)) hpz ≫ Ar ≫ (C).hom := by
  have H := coefficientShearTorusReflection_actionPair hπ data S r j hj a ha hr h3 h4 h6
    p (z ≫ Lr (-(Ur).a₁) (middle_second_root Ur)) hpz
  refine Eq.trans ?_ H
  apply congrArg (fun f => f ≫ As)
  apply pullback.hom_ext
  · simp only [pullback.lift_fst]
  · simp only [pullback.lift_snd]
    exact (coefficientShearLineReflection_second hπ data S r j k hj hk hr
      hscale hp hd3 hd4 z).symm

end FLT.Mazur.WeierstrassDividedDepth
