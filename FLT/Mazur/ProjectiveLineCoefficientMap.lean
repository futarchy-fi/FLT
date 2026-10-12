/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineScaling
public import FLT.Mazur.WeierstrassSplitNodalLaurentCoefficient

/-!
# Coefficient maps of the original glued projective line

Glue the polynomial coefficient maps along both original Laurent transitions.
The result preserves the full affine charts, the base projection and their scalings.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.ProjectiveLine
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K L : Type u} [Field K] [Field L] (f : K →+* L)
local notation "P" => Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f))
local notation "Q" => Spec.map (CommRingCat.ofHom (nodalLaurentCoefficientMap f))

/-- Polynomial coefficient change commutes with the original first Laurent transition. -/
theorem overlapLeft_coefficient : overlapLeft L ≫ P = Q ≫ overlapLeft K := by
  have h : (Polynomial.toLaurent : L[X] →+* L[T;T⁻¹]).comp (Polynomial.mapRingHom f) =
      (nodalLaurentCoefficientMap f).comp Polynomial.toLaurent := by
    apply Polynomial.ringHom_ext
    · intro x
      simpa only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
        Polynomial.toLaurent_C, LaurentPolynomial.C_eq_algebraMap] using
        (nodalLaurentCoefficientMap_scalar f x).symm
    · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
        Polynomial.toLaurent_X, nodalLaurentCoefficientMap_character]
  simpa only [CommRingCat.ofHom_comp, Spec.map_comp, overlapLeft] using
    congrArg (fun h => Spec.map (CommRingCat.ofHom h)) h

/-- Coefficient change also preserves the inverse-coordinate Laurent transition. -/
theorem overlapRight_coefficient : overlapRight L ≫ P = Q ≫ overlapRight K := by
  have h : (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent).comp
      (Polynomial.mapRingHom f) = (nodalLaurentCoefficientMap f).comp
        (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent) := by
    apply Polynomial.ringHom_ext
    · intro x
      change LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.map f (Polynomial.C x))) =
        nodalLaurentCoefficientMap f (LaurentPolynomial.invert
          (Polynomial.toLaurent (Polynomial.C x)))
      rw [Polynomial.map_C, Polynomial.toLaurent_C, Polynomial.toLaurent_C,
        LaurentPolynomial.invert_C, LaurentPolynomial.invert_C]
      simpa only [LaurentPolynomial.C_eq_algebraMap] using
        (nodalLaurentCoefficientMap_scalar f x).symm
    · simp
  simpa only [overlapRight, inversion_hom, overlapLeft, CommRingCat.ofHom_comp,
    Spec.map_comp, Category.assoc] using
      congrArg (fun h => Spec.map (CommRingCat.ofHom h)) h

/-- The actual coefficient map on the whole glued projective line. -/
def coefficientMap : scheme L ⟶ scheme K :=
  pushout.desc (P ≫ left K) (P ≫ right K) (by
    rw [← Category.assoc, overlapLeft_coefficient, Category.assoc,
      overlap_condition, ← Category.assoc, ← overlapRight_coefficient, Category.assoc])

/-- The full first chart retains its polynomial coefficient map. -/
@[reassoc] theorem left_coefficientMap : left L ≫ coefficientMap f = P ≫ left K :=
  pushout.inl_desc _ _ _

/-- The full second chart retains that same polynomial coefficient map. -/
@[reassoc] theorem right_coefficientMap : right L ≫ coefficientMap f = P ≫ right K :=
  pushout.inr_desc _ _ _

/-- The affine coefficient map has its actual coefficient-spectrum projection. -/
@[reassoc] theorem chart_coefficient_toBase :
    P ≫ chartToBase K = chartToBase L ≫ Spec.map (CommRingCat.ofHom f) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (fun x => Polynomial.map_C f (a := x)))

/-- The complete projective coefficient map preserves the base projection on both charts. -/
@[reassoc] theorem coefficientMap_toBase :
    coefficientMap f ≫ toBase K = toBase L ≫ Spec.map (CommRingCat.ofHom f) := by
  apply pushout.hom_ext
  · change left L ≫ _ = left L ≫ _
    rw [left_coefficientMap_assoc, left_toBase, left_toBase_assoc, chart_coefficient_toBase]
  · change right L ≫ _ = right L ≫ _
    rw [right_coefficientMap_assoc, right_toBase, right_toBase_assoc, chart_coefficient_toBase]

/-- Full affine scalings commute with the actual coefficient map. -/
@[reassoc] theorem chartScaling_coefficient (a : Kˣ) (b : Lˣ) (hab : Units.map f a = b) :
    chartScaling L b ≫ P = P ≫ chartScaling K a := by
  subst b
  have h : (PolygonChartScaling.affine (Units.map f a)).comp (Polynomial.mapRingHom f) =
      (Polynomial.mapRingHom f).comp (PolygonChartScaling.affine a) := by
    ext x <;> simp
  simpa only [CommRingCat.ofHom_comp, Spec.map_comp, chartScaling] using
    congrArg (fun h => Spec.map (CommRingCat.ofHom h)) h

end FLT.Mazur.ProjectiveLine
