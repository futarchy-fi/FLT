/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothMixedCover
public import FLT.Mazur.WeierstrassSmoothTransportedComparison

/-!
# Addition on every smooth mixed projective input product

The full smooth affine law and the original polynomial output-Z law agree
on their scheme-theoretic intersection. They glue on all smooth Y/Z and Z/Y
pairs, and on Z/Z pairs, without a discriminant assumption.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (b c : Bool)

/-- The transported affine and polynomial smooth outputs agree on arbitrary common schemes. -/
theorem smoothAffineOverlap_polynomial_smooth (t : Fin 3) {X : Scheme.{u}}
    (f : X ⟶ (smoothAffineOverlapOpen W b c).toScheme)
    (g : X ⟶ (polynomialSmoothInputOpen W
      (productChartCoordinate b) (productChartCoordinate c) t).toScheme)
    (h : f ≫ smoothAffineOverlapInput W b c = g ≫ smoothPolynomialInput W b c t) :
    f ≫ smoothAffineOverlapAddition W b c =
      g ≫ polynomialSmoothChart W (productChartCoordinate b) (productChartCoordinate c) t := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  simp only [Category.assoc, polynomialSmoothChart_inclusion]
  have he := smoothAffineOverlap_polynomial W b c t f
    (g ≫ (polynomialSmoothInputOpen W
      (productChartCoordinate b) (productChartCoordinate c) t).ι)
    (by simpa only [smoothPolynomialInput, Category.assoc] using h)
  simpa only [Category.assoc] using he

/-- Transported smooth affine addition preserves the coefficient morphism of its input chart. -/
theorem smoothAffineOverlapAddition_structure :
    smoothAffineOverlapAddition W b c ≫ integralSmoothStructure W =
      smoothAffineOverlapInput W b c ≫ Spec.map (CommRingCat.ofHom
        (algebraMap R (ChartProduct W (productChartCoordinate b) (productChartCoordinate c)))) := by
  have hb : affineInputOverlapMap W (productChartCoordinate b) (productChartCoordinate c) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (AffineProduct W))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (ProductOverlap W
        (productChartCoordinate b) (productChartCoordinate c) 2 2))) :=
    specAlgHom_structure (productOverlapOther W
      (productChartCoordinate b) (productChartCoordinate c) 2 2)
  rw [smoothAffineOverlapAddition, Category.assoc, smoothAffineAddition_structure,
    smoothAffineOverlapToInputs_inclusion_assoc, hb, smoothAffineOverlapInput, Category.assoc]
  exact congrArg (fun g => (smoothAffineOverlapOpen W b c).ι ≫ g)
    (specAlgHom_structure (productOverlapRestriction W
      (productChartCoordinate b) (productChartCoordinate c) 2 2)).symm

/-- The two original smooth local addition morphisms for a mixed input product. -/
def smoothMixedLocal (d : Bool) :
    smoothMixedDomain W b c d ⟶ (integralSmoothOpen W).toScheme :=
  match d with
  | true => smoothAffineOverlapAddition W b c
  | false => polynomialSmoothChart W (productChartCoordinate b) (productChartCoordinate c) 2

/-- The two local smooth laws agree for every pair of presentations of the same input. -/
theorem smoothMixedLocal_commonScheme (d e : Bool) {X : Scheme.{u}}
    (f : X ⟶ smoothMixedDomain W b c d) (g : X ⟶ smoothMixedDomain W b c e)
    (h : f ≫ smoothMixedInclusion W b c d = g ≫ smoothMixedInclusion W b c e) :
    f ≫ smoothMixedLocal W b c d = g ≫ smoothMixedLocal W b c e := by
  cases d <;> cases e
  · have he := (cancel_mono (smoothMixedInclusion W b c false)).mp h
    exact congrArg (fun a => a ≫ smoothMixedLocal W b c false) he
  · symm
    apply smoothAffineOverlap_polynomial_smooth W b c 2 g f
    have he := congrArg (fun a => a ≫ (smoothProductChartOpen W b c).ι) h.symm
    simpa only [Category.assoc, smoothMixedInclusion,
      smoothAffineOverlapToChart_inclusion, smoothPolynomialToInputs_inclusion] using he
  · apply smoothAffineOverlap_polynomial_smooth W b c 2 f g
    have he := congrArg (fun a => a ≫ (smoothProductChartOpen W b c).ι) h
    simpa only [Category.assoc, smoothMixedInclusion,
      smoothAffineOverlapToChart_inclusion, smoothPolynomialToInputs_inclusion] using he
  · have he := (cancel_mono (smoothMixedInclusion W b c true)).mp h
    exact congrArg (fun a => a ≫ smoothMixedLocal W b c true) he

variable (ha : b = false ∨ c = false)

/-- Addition on the full smooth input product whenever at least one input chart is affine. -/
def smoothMixedAddition :
    (smoothProductChartOpen W b c).toScheme ⟶ (integralSmoothOpen W).toScheme :=
  (smoothMixedCover W b c ha).glueMorphisms (smoothMixedLocal W b c)
    (fun d e => smoothMixedLocal_commonScheme W b c d e _ _ pullback.condition)

/-- The glued smooth mixed law retains both original local formulas. -/
@[reassoc] theorem smoothMixedLocal_glued (d : Bool) :
    smoothMixedInclusion W b c d ≫ smoothMixedAddition W b c ha = smoothMixedLocal W b c d :=
  (smoothMixedCover W b c ha).ι_glueMorphisms _ _ d

/-- The glued mixed addition is a morphism over the original coefficient spectrum. -/
theorem smoothMixedAddition_structure :
    smoothMixedAddition W b c ha ≫ integralSmoothStructure W =
      (smoothProductChartOpen W b c).ι ≫ Spec.map (CommRingCat.ofHom
        (algebraMap R (ChartProduct W (productChartCoordinate b) (productChartCoordinate c)))) := by
  apply (smoothMixedCover W b c ha).hom_ext
  intro d
  change smoothMixedInclusion W b c d ≫ _ = smoothMixedInclusion W b c d ≫ _
  rw [← Category.assoc, smoothMixedLocal_glued]
  cases d
  · change polynomialSmoothChart W _ _ 2 ≫ _ = smoothPolynomialToInputs W b c 2 ≫ _
    rw [polynomialSmoothChart_structure, smoothPolynomialToInputs_inclusion_assoc,
      smoothPolynomialInput, Category.assoc, projectiveAdditionInclusion,
      specAlgHom_structure (additionOutputRestriction W
        (productChartCoordinate b) (productChartCoordinate c) 2)]
  · change smoothAffineOverlapAddition W b c ≫ _ = smoothAffineOverlapToChart W b c ≫ _
    rw [smoothAffineOverlapAddition_structure, smoothAffineOverlapToChart_inclusion_assoc]

/-- The two original local formulas uniquely determine the smooth mixed addition morphism. -/
theorem smoothMixedAddition_unique
    (f : (smoothProductChartOpen W b c).toScheme ⟶ (integralSmoothOpen W).toScheme)
    (hf : ∀ d, smoothMixedInclusion W b c d ≫ f = smoothMixedLocal W b c d) :
    f = smoothMixedAddition W b c ha := by
  apply (smoothMixedCover W b c ha).hom_ext
  intro d
  exact (hf d).trans (smoothMixedLocal_glued W b c ha d).symm

end FLT.Mazur.WeierstrassIntegralChart
