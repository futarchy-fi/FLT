/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicRelativeDimension
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! # Integral affine coordinates and dense overlap

The ordinary chart and the common open subset are integral over a domain.
These results do not yet establish connectedness of the full glued scheme. -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Reorder x,y so that y is the outer variable in the bivariate polynomial ring. -/
def bivariateCoordinates : MvPolynomial (Fin 2) R ≃ₐ[R] Polynomial (Polynomial R) :=
  ((renameEquiv R (Equiv.swap (0 : Fin 2) 1)).trans (finSuccEquiv R 1)).trans
    (Polynomial.mapAlgEquiv (uniqueAlgEquiv R (Fin 1)))

@[simp] theorem bivariateCoordinates_C (r : R) :
    bivariateCoordinates (R := R) (C r) = Polynomial.C (Polynomial.C r) := by
  exact (bivariateCoordinates (R := R)).commutes r

@[simp] theorem bivariateCoordinates_X_zero :
    bivariateCoordinates (R := R) (X 0) = Polynomial.C Polynomial.X := by
  simp only [bivariateCoordinates, AlgEquiv.trans_apply, renameEquiv_apply,
    rename_X, Equiv.swap_apply_left, finSuccEquiv_apply, eval₂Hom_X']
  change Polynomial.map (uniqueAlgEquiv R (Fin 1)).toRingHom
    (Polynomial.C (X (0 : Fin 1))) = _
  rw [Polynomial.map_C]
  exact congrArg Polynomial.C (eval₂_X _ _ _)

@[simp] theorem bivariateCoordinates_X_one :
    bivariateCoordinates (R := R) (X 1) = Polynomial.X := by
  simp [bivariateCoordinates, finSuccEquiv_apply]

/-- The affine gluing equation agrees with the library's Weierstrass polynomial. -/
theorem bivariateCoordinates_equation :
    bivariateCoordinates (equation W false) = W.toAffine.polynomial := by
  simp [equation, map_sub, map_add, map_mul, map_pow, Affine.polynomial]
  ring

/-- The ordinary chart ring is the established Weierstrass coordinate algebra. -/
def affineCoordinateRingEquiv : Ring W false ≃ₐ[R] W.toAffine.CoordinateRing :=
  Ideal.quotientEquivAlg (Ideal.span {equation W false}) _
    (bivariateCoordinates (R := R)) (by
      rw [Ideal.map_span, Set.image_singleton]
      exact congrArg (fun f ↦ Ideal.span {f}) (bivariateCoordinates_equation W).symm)

/-- The ordinary chart ring is integral over any integral coefficient ring. -/
instance affineRing_isDomain [IsDomain R] : IsDomain (Ring W false) :=
  (affineCoordinateRingEquiv W).injective.isDomain

@[simp] theorem affineCoordinateRingEquiv_coord_one :
    affineCoordinateRingEquiv W (coord W false 1) =
      Affine.CoordinateRing.mk W.toAffine Polynomial.X := by
  change Ideal.Quotient.mk _ (bivariateCoordinates (X 1)) = _
  rw [bivariateCoordinates_X_one]
  rfl

/-- The overlap coordinate is nonzero even for a singular Weierstrass cubic. -/
theorem affine_coord_one_ne_zero [IsDomain R] : coord W false 1 ≠ 0 := by
  intro h
  have h' := congrArg (affineCoordinateRingEquiv W) h
  rw [affineCoordinateRingEquiv_coord_one, map_zero] at h'
  exact (Affine.CoordinateRing.basis W.toAffine).ne_zero 1
    (by simpa only [Affine.CoordinateRing.basis_one] using h')

/-- Inverting the overlap coordinate preserves the integral affine ring. -/
instance affineOverlap_isDomain [IsDomain R] : IsDomain (Overlap W false) :=
  Localization.Away.isDomain (affine_coord_one_ne_zero W)

/-- The transition isomorphism makes the infinity-side overlap integral as well. -/
instance infinityOverlap_isDomain [IsDomain R] : IsDomain (Overlap W true) :=
  (overlapEquiv W).symm.injective.isDomain

/-- The ordinary affine chart is irreducible over an integral coefficient ring. -/
instance affineChart_irreducibleSpace [IsDomain R] : IrreducibleSpace (chart W false) :=
  inferInstanceAs (IrreducibleSpace (PrimeSpectrum (Ring W false)))

/-- The common open subset is irreducible in either chart presentation. -/
instance overlap_irreducibleSpace [IsDomain R] (b : Bool) :
    IrreducibleSpace (Spec (.of (Overlap W b))) := by
  cases b <;> exact inferInstanceAs (IrreducibleSpace (PrimeSpectrum _))

/-- The common open subset is dense in the ordinary affine chart. -/
theorem affineOverlap_denseRange [IsDomain R] : DenseRange (overlapInclusion W false) :=
  (overlapInclusion W false).isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace _

end WeierstrassCurve.CubicCharts
