/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityChartCompatibility
public import FLT.Mazur.WeierstrassProductOverlap

/-!
# Concrete intersections of infinity and polynomial addition domains

Localize the infinity domain at the polynomial output coordinate. The resulting
ring receives both domain restrictions and has their common-restriction universal
property. For output Y the two actual addition maps agree on this concrete ring.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (t : Fin 3)

/-- Intersection of the infinity domain with a polynomial output-coordinate open. -/
abbrev InfinityProjectiveOverlap := Localization.Away
  (infinityAdditionRestriction W (chartProductAdditionCoordinates W 1 1 t))

/-- The intersection restricts the infinity domain by a single principal localization. -/
def infinityProjectiveRestriction :
    InfinityAdditionOpen W →ₐ[R] InfinityProjectiveOverlap W t :=
  IsScalarTower.toAlgHom R (InfinityAdditionOpen W) (InfinityProjectiveOverlap W t)

/-- The polynomial output coordinate is invertible on the concrete intersection. -/
theorem infinityProjective_isUnit :
    IsUnit ((infinityProjectiveRestriction W t).comp (infinityAdditionRestriction W)
      (chartProductAdditionCoordinates W 1 1 t)) :=
  IsLocalization.Away.algebraMap_isUnit
    (infinityAdditionRestriction W (chartProductAdditionCoordinates W 1 1 t))

/-- The concrete intersection also receives the polynomial-domain restriction. -/
def infinityProjectivePolynomial :
    AdditionOutputOpen W 1 1 t →ₐ[R] InfinityProjectiveOverlap W t :=
  IsLocalization.Away.liftAlgHom (chartProductAdditionCoordinates W 1 1 t)
    (infinityProjective_isUnit W t)

/-- Both input restrictions are the same algebra map on the actual intersection. -/
theorem infinityProjective_inputs :
    (infinityProjectivePolynomial W t).comp (additionOutputRestriction W 1 1 t) =
      (infinityProjectiveRestriction W t).comp (infinityAdditionRestriction W) := by
  apply AlgHom.coe_ringHom_injective
  exact IsLocalization.Away.lift_comp (chartProductAdditionCoordinates W 1 1 t)
    (S := AdditionOutputOpen W 1 1 t)
    (g := ((infinityProjectiveRestriction W t).comp (infinityAdditionRestriction W)).toRingHom)
    (infinityProjective_isUnit W t)

/-- Every common restriction of the two domains factors through this concrete ring. -/
def infinityProjectiveLift (f : AdditionOutputOpen W 1 1 t →ₐ[R] S)
    (g : InfinityAdditionOpen W →ₐ[R] S)
    (h : f.comp (additionOutputRestriction W 1 1 t) =
      g.comp (infinityAdditionRestriction W)) : InfinityProjectiveOverlap W t →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom
    (infinityAdditionRestriction W (chartProductAdditionCoordinates W 1 1 t))
    (show IsUnit (g (infinityAdditionRestriction W
      (chartProductAdditionCoordinates W 1 1 t))) by
      have hu := (additionOutput_isUnit W 1 1 t).map f
      rw [show f (additionOutputRestriction W 1 1 t
          (chartProductAdditionCoordinates W 1 1 t)) =
        g (infinityAdditionRestriction W (chartProductAdditionCoordinates W 1 1 t)) from
          DFunLike.congr_fun h _] at hu
      exact hu)

/-- The universal lift retains the original infinity-domain map. -/
@[simp] theorem infinityProjectiveLift_infinity
    (f : AdditionOutputOpen W 1 1 t →ₐ[R] S) (g : InfinityAdditionOpen W →ₐ[R] S)
    (h : f.comp (additionOutputRestriction W 1 1 t) =
      g.comp (infinityAdditionRestriction W)) :
    (infinityProjectiveLift W t f g h).comp (infinityProjectiveRestriction W t) = g := by
  apply AlgHom.ext
  intro a
  change infinityProjectiveLift W t f g h (algebraMap _ _ a) = g a
  simp only [infinityProjectiveLift, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

/-- The universal lift also retains the polynomial-domain map. -/
@[simp] theorem infinityProjectiveLift_polynomial
    (f : AdditionOutputOpen W 1 1 t →ₐ[R] S) (g : InfinityAdditionOpen W →ₐ[R] S)
    (h : f.comp (additionOutputRestriction W 1 1 t) =
      g.comp (infinityAdditionRestriction W)) :
    (infinityProjectiveLift W t f g h).comp (infinityProjectivePolynomial W t) = f := by
  apply IsLocalization.algHom_ext (Submonoid.powers (chartProductAdditionCoordinates W 1 1 t))
  change ((infinityProjectiveLift W t f g h).comp (infinityProjectivePolynomial W t)).comp
    (additionOutputRestriction W 1 1 t) = f.comp (additionOutputRestriction W 1 1 t)
  rw [AlgHom.comp_assoc, infinityProjective_inputs, ← AlgHom.comp_assoc,
    infinityProjectiveLift_infinity, h]

/-- Factorization through the concrete intersection is unique. -/
theorem infinityProjective_hom_ext {f g : InfinityProjectiveOverlap W t →ₐ[R] S}
    (h : f.comp (infinityProjectiveRestriction W t) =
      g.comp (infinityProjectiveRestriction W t)) : f = g :=
  IsLocalization.algHom_ext
    (Submonoid.powers (infinityAdditionRestriction W
      (chartProductAdditionCoordinates W 1 1 t))) h

/-- The Y-output polynomial and infinity maps agree on their concrete intersection. -/
theorem infinityProjective_y_addition :
    (infinityProjectivePolynomial W 1).comp (projectiveAdditionChart W 1 1 1) =
      (infinityProjectiveRestriction W 1).comp (infinityAdditionChart W) :=
  infinityAdditionChart_compatibility W _ _ (infinityProjective_inputs W 1)

end FLT.Mazur.WeierstrassIntegralChart
