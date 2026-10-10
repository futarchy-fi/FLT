/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralTripleFlat
public import FLT.Mazur.WeierstrassReciprocalOutputRegular
public import FLT.Mazur.WeierstrassInfinityInputMinorRegular
public import FLT.Mazur.WeierstrassAffineOutputDomains

/-!
# Regular intermediate outputs on arbitrary flat triple domains

An inner-law projection is flat because its composite into the global product
is a flat original-pair projection. This transports the regularity of reciprocal
and infinity outputs to any open member of the actual triple cover.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Either original pair of the triple product, before applying any addition. -/
def tripleInnerPair (b : Bool) : integralCurveTriple W ⟶ integralCurveProduct W :=
  if b then integralCurveTripleLastPair W else integralCurveTriplePair W

/-- Both original pair projections are flat. -/
instance tripleInnerPair_flat (b : Bool) : Flat (tripleInnerPair W b) := by
  cases b
  · exact integralCurveTriplePair_flat W
  · exact integralCurveTripleLastPair_flat W

/-- Restricting a flat triple domain to a genuine inner-law open gives a flat projection. -/
theorem tripleInnerLaw_flat {X Y : Scheme.{u}} (t : X ⟶ integralCurveTriple W) [Flat t]
    (b : Bool) (d : Y ⟶ integralCurveProduct W) [IsOpenImmersion d]
    (f : X ⟶ Y) (h : f ≫ d = t ≫ tripleInnerPair W b) : Flat f := by
  apply MorphismProperty.of_postcomp @Flat f d (inferInstance : IsOpenImmersion d)
  rw [h]
  infer_instance

/-- Every affine-input inner law, including a reciprocal one, has regular output Z. -/
theorem tripleInnerAffine_output_z_regular {X : Scheme.{u}}
    (t : X ⟶ integralCurveTriple W) [Flat t] (b : Bool) (i : AdditionChartIndex)
    (f : X ⟶ Spec (additionChartRing W i))
    (h : f ≫ additionGlobalDomain W i = t ≫ tripleInnerPair W b) :
    IsRegular (specSectionHom f
      (additionChartAlgOutput W i (coord W (additionChartOutput i) 2))) := by
  let _ := tripleInnerLaw_flat W t b (additionGlobalDomain W i) f h
  exact additionChart_output_z_regular_sections W i f

/-- The genuine infinity inner law also has regular output Z on every flat triple domain. -/
theorem tripleInnerInfinity_output_z_regular {X : Scheme.{u}}
    (t : X ⟶ integralCurveTriple W) [Flat t] (b : Bool)
    (f : X ⟶ Spec (.of (InfinityAdditionOpen W)))
    (h : f ≫ infinityGlobalDomain W = t ≫ tripleInnerPair W b) :
    IsRegular (specSectionHom f (infinityAdditionChart W (coord W 1 2))) := by
  let _ := tripleInnerLaw_flat W t b (infinityGlobalDomain W) f h
  exact specSectionHom_isRegular f (infinityAdditionChart_z_regular W)

/-- The genuine first inner-law projection on every full-cover member is flat. -/
theorem tripleFull_innerLeft_flat (hΔ : IsUnit W.Δ)
    (i : (integralCurveTripleFullCover W hΔ).I₀) :
    Flat (integralCurveTripleFullInner W hΔ i ≫
      integralCurveTripleInnerLeftDomain W hΔ i.2) := by
  apply tripleInnerLaw_flat W ((integralCurveTripleFullCover W hΔ).f i) false
    ((integralCurveAdditionCover W hΔ).f i.2.1)
  rw [Category.assoc, integralCurveTripleInnerLeftDomain_inputs, ← Category.assoc,
    integralCurveTripleFullInner_inputs]
  rfl

/-- The genuine last inner-law projection on every full-cover member is flat. -/
theorem tripleFull_innerRight_flat (hΔ : IsUnit W.Δ)
    (i : (integralCurveTripleFullCover W hΔ).I₀) :
    Flat (integralCurveTripleFullInner W hΔ i ≫
      integralCurveTripleInnerRightDomain W hΔ i.2) := by
  apply tripleInnerLaw_flat W ((integralCurveTripleFullCover W hΔ).f i) true
    ((integralCurveAdditionCover W hΔ).f i.2.2)
  rw [Category.assoc, integralCurveTripleInnerRightDomain_inputs, ← Category.assoc,
    integralCurveTripleFullInner_inputs]
  rfl

end FLT.Mazur.WeierstrassIntegralChart
