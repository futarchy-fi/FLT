/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicSmooth

/-! # Relative dimension of the smooth Weierstrass scheme -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Derivative charts have relative dimension one as ring morphisms. -/
theorem derivativeRing_dimension_one (b : Bool) (i : Fin 2) :
    RingHom.IsStandardSmoothOfRelativeDimension 1
      (algebraMap R (DerivativeRing W b i)) :=
  (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr inferInstance

/-- The affine chart is locally standard smooth of dimension one. -/
theorem affineRing_locally_dimension_one [W.IsElliptic] :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap R (Ring W false)) := by
  apply RingHom.locally_of_exists RingHom.isStandardSmoothOfRelativeDimension_respectsIso
    (algebraMap R _) (derivative W false) (affine_derivatives_span W) (DerivativeRing W false)
  intro i
  rw [← IsScalarTower.algebraMap_eq]
  exact derivativeRing_dimension_one W false i

/-- The infinity overlap inherits relative dimension one through the chart equivalence. -/
theorem infinityOverlap_locally_dimension_one [W.IsElliptic] :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap R (Overlap W true)) := by
  have h := RingHom.locally_stableUnderCompositionWithLocalizationAwayTarget
    (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway 1).2
    (Overlap W false) (coord W false 1) (algebraMap R (Ring W false))
    (affineRing_locally_dimension_one W)
  rw [← IsScalarTower.algebraMap_eq] at h
  have h' := (RingHom.locally_respectsIso
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso).left
      (algebraMap R (Overlap W false)) (overlapEquiv W).toRingEquiv h
  have he : (overlapEquiv W).toRingEquiv.toRingHom.comp (algebraMap R (Overlap W false)) =
      algebraMap R (Overlap W true) := by
    ext r
    exact (overlapEquiv W).commutes r
  rwa [he] at h'

/-- The whole infinity chart is locally standard smooth of dimension one. -/
theorem infinityRing_locally_dimension_one [W.IsElliptic] :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap R (Ring W true)) := by
  apply RingHom.locally_ofLocalizationSpanTarget
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso (algebraMap R _)
    {coord W true 1, derivative W true 1} (infinity_smooth_span W)
  rintro ⟨r, hr⟩
  rcases hr with rfl | hr
  · rw [← IsScalarTower.algebraMap_eq]
    exact infinityOverlap_locally_dimension_one W
  · rcases Set.mem_singleton_iff.mp hr with rfl
    rw [← IsScalarTower.algebraMap_eq]
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
      (derivativeRing_dimension_one W true 1)

/-- Both affine chart projections are smooth of relative dimension one. -/
instance chartToBase_dimension_one [W.IsElliptic] (b : Bool) :
    SmoothOfRelativeDimension 1 (chartToBase W b) := by
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mpr
  cases b
  · exact affineRing_locally_dimension_one W
  · exact infinityRing_locally_dimension_one W

/-- The proper smooth Weierstrass scheme has relative dimension one. -/
instance toBase_dimension_one [W.IsElliptic] : SmoothOfRelativeDimension 1 (toBase W) := by
  apply IsZariskiLocalAtSource.of_openCover
    (P := @SmoothOfRelativeDimension 1) (sourceOpenCover W)
  intro b
  change SmoothOfRelativeDimension 1 (sourceChart W b ≫ toBase W)
  cases b
  · change SmoothOfRelativeDimension 1 (affineChart W ≫ toBase W)
    rw [affineChart_toBase]
    infer_instance
  · change SmoothOfRelativeDimension 1 (infinityChart W ≫ toBase W)
    rw [infinityChart_toBase]
    infer_instance

/-- The infinity section ensures every base point has a point in its fiber. -/
instance toBase_surjective : Surjective (toBase W) where
  surj x := ⟨infinity W x, congrArg (fun f ↦ f x) (infinity_toBase W)⟩

end WeierstrassCurve.CubicCharts
