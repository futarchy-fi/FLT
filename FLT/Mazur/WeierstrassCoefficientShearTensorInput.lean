/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXTensorOriginal
public import FLT.Mazur.WeierstrassCoefficientShearUnitSlope
public import FLT.Mazur.WeierstrassRootShearSlopeInput

/-!
# The actual scale-one tensor input equals the root-sheared torus input

The complete original affine contraction agrees with the ordered Laurent
parameter followed by the proper cubic shear. All functions are compared,
over arbitrary coefficient algebras, without a discriminant-unit condition.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open WeierstrassIntegralChart WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (S : Type) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S s = 1) (hb3 : algebraMap R S b3 = 0)
  (hb4 : algebraMap R S b4 = 0) (hb6 : algebraMap R S b6 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (W.map (algebraMap R S)).a₁ + 2 * r)
local notation "V" => W.map (algebraMap R S)
local notation "T" => ScalarExtension W s b3 b4 b6 S
local notation "f" => tensorOriginalAffineMap W s b3 b4 b6 h3 h4 h6 S
local notation "L" => tensorShearScaleOneLaurentMap W s b3 b4 b6 S r hs hb3 hb4 hb6 hr

include h3 h4 h6 hb3 hb4 hb6 in
/-- Vanishing divided coefficients force the original specialized cubic to be nodal form. -/
theorem tensorOriginal_nodal_coefficients : (V).a₃ = 0 ∧ (V).a₄ = 0 ∧ (V).a₆ = 0 := by
  change algebraMap R S W.a₃ = 0 ∧ algebraMap R S W.a₄ = 0 ∧ algebraMap R S W.a₆ = 0
  simp only [h3, h4, h6, map_mul, hb3, hb4, hb6, mul_zero, and_self]

local notation "g3" => And.left
  (tensorOriginal_nodal_coefficients W s b3 b4 b6 h3 h4 h6 S hb3 hb4 hb6)
local notation "g4" => And.left (And.right
  (tensorOriginal_nodal_coefficients W s b3 b4 b6 h3 h4 h6 S hb3 hb4 hb6))
local notation "g6" => And.right (And.right
  (tensorOriginal_nodal_coefficients W s b3 b4 b6 h3 h4 h6 S hb3 hb4 hb6))
local notation "I" => rootShearTorusSmoothIso V r a ha hr g3 g4 g6

/-- Every original tensor cubic function agrees with the full root-sheared torus input. -/
theorem tensorShearScaleOne_originalInput :
    Spec.map (CommRingCat.ofHom (f).toRingHom) ≫ integralCurveChart V 2 =
      Spec.map (CommRingCat.ofHom (L).toRingHom) ≫ (I).hom ≫ (integralSmoothOpen V).ι := by
  have ha' : (a : S) = (rootShearCurve V r).a₁ :=
    ha.trans (rootShearCurve_coefficients (W := V) r).1.symm
  let e := tensorShearUnitSlopeEquiv W s b3 b4 b6 S r hs hb3 hb4 hb6 hr a ha'
  have hx : (e.toAlgHom.comp f) (coord V 2 0) =
      slopeZ (a : S) * (slopeZ (a : S) + algebraMap S (SlopeOpen (a : S)) (a : S)) := by
    change e (f (coord V 2 0)) = _
    rw [tensorOriginalAffineMap_x]
    exact tensorShearUnitSlopeEquiv_x W s b3 b4 b6 S r hs hb3 hb4 hb6 hr a ha'
  have hy : (e.toAlgHom.comp f) (coord V 2 1) =
      (slopeZ (a : S) * (slopeZ (a : S) + algebraMap S (SlopeOpen (a : S)) (a : S))) *
        (slopeZ (a : S) + algebraMap S (SlopeOpen (a : S)) r) := by
    change e (f (coord V 2 1)) = _
    rw [tensorOriginalAffineMap_y]
    exact tensorShearUnitSlopeEquiv_y W s b3 b4 b6 S r hs hb3 hb4 hb6 hr a ha'
  have hc := rootShearSlopeInput_toCurve a V r ha hr g3 g4 g6 (e.toAlgHom.comp f) hx hy
  have hl := tensorShearUnitSlopeEquiv_laurent W s b3 b4 b6 S r hs hb3 hb4 hb6 hr a ha'
  rw [← hl] at hc
  let J := Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op
  apply (cancel_epi J.hom).mp
  change Spec.map _ ≫ (Spec.map _ ≫ _) = Spec.map _ ≫ Spec.map _ ≫ _ ≫ _
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  exact hc

/-- Any independent smooth lift of the actual tensor input is exactly its torus parameter. -/
theorem tensorShearScaleOne_smoothInput_unique
    (p : Spec (.of T) ⟶ (integralSmoothOpen V).toScheme)
    (hp : p ≫ (integralSmoothOpen V).ι =
      Spec.map (CommRingCat.ofHom (f).toRingHom) ≫ integralCurveChart V 2) :
    p = Spec.map (CommRingCat.ofHom (L).toRingHom) ≫ (I).hom := by
  apply (cancel_mono (integralSmoothOpen V).ι).mp
  rw [hp, Category.assoc]
  exact tensorShearScaleOne_originalInput W s b3 b4 b6 h3 h4 h6 S r
    hs hb3 hb4 hb6 hr a ha

end FLT.Mazur.WeierstrassModificationX
