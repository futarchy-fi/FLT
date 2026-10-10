/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginIdealAffine

/-!
# The actual origin is a relative effective Cartier divisor

The explicit parameter neighborhood and the original affine chart give
regular equations for the intrinsic origin ideal over an arbitrary base ring.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The original parameter is a regular global equation on its actual neighborhood. -/
theorem originIdealSheaf_cartierChart :
    FCurve.CartierChart (originNeighborhoodSection W).ker ⟨⊤, isAffineOpen_top _⟩ := by
  let e := (Scheme.ΓSpecIso (.of (OriginNeighborhood W))).commRingCatIsoToRingEquiv
  refine ⟨e.symm (originCoordinate W 0),
    flatRingHom_isRegular e.symm.toRingHom (.of_bijective e.symm.bijective)
      (originCoordinate_x_regular W), ?_⟩
  have hc : Ideal.map e.toRingHom
      ((originNeighborhoodSection W).ker.ideal ⟨⊤, isAffineOpen_top _⟩) =
      Ideal.span {originCoordinate W 0} :=
    (Ideal.map_comap_of_equiv e).trans (originIdealSheaf_coordinate W)
  have h := congrArg (Ideal.map e.symm.toRingHom) hc
  simpa only [RingEquiv.toRingHom_eq_coe, Ideal.map_of_equiv,
    Ideal.map_span, Set.image_singleton, RingEquiv.coe_toRingHom] using h

/-- The actual two-chart cover proves the intrinsic origin ideal is effective Cartier. -/
theorem originIdealSheaf_effectiveCartier : FCurve.EffectiveCartier (integralCurveZero W).ker := by
  intro x
  rcases originNeighborhood_affine_cover W x with ⟨y, hy⟩ | ⟨y, hy⟩
  · let f := originNeighborhoodInclusion W
    let U : (Spec (.of (OriginNeighborhood W))).affineOpens := ⟨⊤, isAffineOpen_top _⟩
    refine ⟨⟨f ''ᵁ U, U.2.image_of_isOpenImmersion f⟩, ⟨y, trivial, hy⟩, ?_⟩
    apply (FCurve.cartierChart_comap_iff _ f U).mp
    rw [originIdealSheaf_neighborhood]
    exact originIdealSheaf_cartierChart W
  · let f := integralCurveChart W 2
    let U : (chartScheme W 2).affineOpens := ⟨⊤, isAffineOpen_top _⟩
    refine ⟨⟨f ''ᵁ U, U.2.image_of_isOpenImmersion f⟩, ⟨y, trivial, hy⟩, ?_⟩
    apply (FCurve.cartierChart_comap_iff _ f U).mp
    rw [originIdealSheaf_affine]
    exact FCurve.cartierChart_top U

/-- The origin divisor is flat over the original coefficient base as well. -/
theorem originIdealSheaf_relativeCartier :
    FCurve.RelativeEffectiveCartier (integralCurveStructure W) (integralCurveZero W).ker :=
  ⟨originIdealSheaf_effectiveCartier W,
    FCurve.flat_sectionImage _ _ (integralCurveZero_structure W)⟩

/-- All original origin powers are effective Cartier, including the zeroth power. -/
theorem originIdealSheaf_power_effectiveCartier (n : ℕ) :
    FCurve.EffectiveCartier ((integralCurveZero W).ker ^ n) :=
  (originIdealSheaf_effectiveCartier W).pow n

end FLT.Mazur.WeierstrassIntegralChart
