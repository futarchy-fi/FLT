/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingEquation
public import FLT.Mazur.WeierstrassSplitNodalRelativeSmooth
public import FLT.Mazur.WeierstrassSmoothCoefficientPreimage

/-!
# The whole smooth locus on a nilpotent smoothing is affine

Reduction modulo the nilradical is surjective on the underlying cubic. Both
its smooth open and its Y chart pull back to those of the original split nodal
cubic. Thus the two opens agree already on the original thickened curve.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OneGonSmoothing

open WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (t : R) (ht : IsNilpotent t)

include ht in
/-- The Y chart is the entire smooth open, retaining every nilpotent coefficient. -/
theorem nilpotent_smoothOpen_eq_chart :
    integralSmoothOpen (equation t) = (integralCurveChart (equation t) 1).opensRange := by
  let S := R ⧸ nilradical R
  have hs : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    ⟨PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical le_rfl |>.2⟩
  have hc : Surjective (integralCoefficientMorphism (S := S) (equation t)) :=
    MorphismProperty.of_isPullback (integralCoefficient_isPullback (S := S) (equation t)).flip
      hs
  have he : (equation t).map (algebraMap R S) = splitNodalEquation (-1 : Sˣ) := by
    rw [equation_map]
    have hz : algebraMap R S t = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ht
    rw [hz]
    rfl
  ext x
  obtain ⟨y, rfl⟩ := (integralCoefficientMorphism (S := S) (equation t)).surjective x
  change y ∈ integralCoefficientMorphism (S := S) (equation t) ⁻¹ᵁ
    integralSmoothOpen (equation t) ↔
      y ∈ integralCoefficientMorphism (S := S) (equation t) ⁻¹ᵁ
        (integralCurveChart (equation t) 1).opensRange
  rw [integralCoefficientMorphism_preimage_smooth,
    integralCoefficientMorphism_preimage_chart]
  have hr : integralSmoothOpen ((equation t).map (algebraMap R S)) =
      (integralCurveChart ((equation t).map (algebraMap R S)) 1).opensRange := by
    rw [he]
    exact TopologicalSpace.Opens.ext (splitNodalRelative_smooth_range (-1 : Sˣ))
  rw [hr]

/-- The actual Y chart identifies the full smooth scheme on every nilpotent smoothing. -/
def nilpotentSmoothChartIso : chartScheme (equation t) 1 ≅
    (integralSmoothOpen (equation t)).toScheme :=
  IsOpenImmersion.isoOfRangeEq (integralCurveChart (equation t) 1)
    (integralSmoothOpen (equation t)).ι (by
      rw [Scheme.Opens.range_ι]
      exact congrArg (fun U : (integralCurve (equation t)).Opens =>
        (U : Set (integralCurve (equation t))))
        (nilpotent_smoothOpen_eq_chart t ht).symm)

include ht in
/-- Affineness holds on the whole original smooth group of the thickened cubic. -/
theorem nilpotent_smooth_isAffine : IsAffine (integralSmoothOpen (equation t)).toScheme :=
  IsAffine.of_isIso (nilpotentSmoothChartIso t ht).inv

end FLT.Mazur.OneGonSmoothing
