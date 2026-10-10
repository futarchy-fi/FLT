/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothAffineDomain

/-!
# Pulling back the actual addition cover to smooth affine inputs

The four original charts cover all smooth affine pairs in every reduction
type. Each pulled-back chart maps to the actual smooth restriction of its
original chart, so its addition output is a morphism to the smooth curve.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The original four-chart cover pulled back to the full smooth affine input open. -/
def smoothAffineAdditionCover : (smoothAffineInputOpen W).toScheme.OpenCover :=
  (affineAdditionDomainCover W).pullback₁ (smoothAffineInputToDomain W)

/-- The projection from a pulled-back domain to the original addition chart. -/
def smoothAffineAdditionProjection (i : AdditionChartIndex) :
    (smoothAffineAdditionCover W).X i ⟶ Spec (additionChartRing W i) :=
  (affineAdditionDomainCover W).pullbackHom (smoothAffineInputToDomain W) i

/-- Both routes from a pulled-back chart to the original affine product coincide. -/
@[reassoc] theorem smoothAffineAdditionProjection_inputs (i : AdditionChartIndex) :
    smoothAffineAdditionProjection W i ≫ additionChartInclusion W i =
      (smoothAffineAdditionCover W).f i ≫ (smoothAffineInputOpen W).ι := by
  rw [← additionChartToDomain_inclusion, ← Category.assoc]
  change ((affineAdditionDomainCover W).pullbackHom _ i ≫
    (affineAdditionDomainCover W).f i) ≫ _ = _
  rw [Scheme.Cover.pullbackHom_map, Category.assoc, smoothAffineInputToDomain_inclusion]
  rfl

/-- A pulled-back domain consists entirely of smooth inputs in its original chart. -/
theorem smoothAffineAdditionProjection_range (i : AdditionChartIndex) :
    Set.range (smoothAffineAdditionProjection W i) ⊆ additionSmoothInputOpen W i := by
  rw [← additionSmoothInputOpen_preimage]
  rintro _ ⟨p, rfl⟩
  change additionChartInclusion W i (smoothAffineAdditionProjection W i p) ∈
    smoothAffineInputOpen W
  have h := congrArg (fun f => f p) (smoothAffineAdditionProjection_inputs W i)
  rw [show additionChartInclusion W i (smoothAffineAdditionProjection W i p) =
      (smoothAffineInputOpen W).ι ((smoothAffineAdditionCover W).f i p) from h]
  exact ((smoothAffineAdditionCover W).f i p).property

/-- The canonical map to the previously constructed restricted smooth chart. -/
def smoothAffineAdditionLift (i : AdditionChartIndex) :
    (smoothAffineAdditionCover W).X i ⟶ (additionSmoothInputOpen W i).toScheme :=
  IsOpenImmersion.lift (additionSmoothInputOpen W i).ι (smoothAffineAdditionProjection W i)
    (by rw [Scheme.Opens.range_ι]; exact smoothAffineAdditionProjection_range W i)

/-- The lift retains the original projection as a scheme morphism. -/
@[reassoc] theorem smoothAffineAdditionLift_inclusion (i : AdditionChartIndex) :
    smoothAffineAdditionLift W i ≫ (additionSmoothInputOpen W i).ι =
      smoothAffineAdditionProjection W i :=
  IsOpenImmersion.lift_fac _ _ _

/-- The restricted chart and cover map determine the same actual input pair. -/
@[reassoc] theorem smoothAffineAdditionLift_inputs (i : AdditionChartIndex) :
    smoothAffineAdditionLift W i ≫ additionSmoothChartInclusion W i =
      (smoothAffineAdditionCover W).f i ≫ (smoothAffineInputOpen W).ι := by
  rw [additionSmoothChartInclusion, smoothAffineAdditionLift_inclusion_assoc,
    smoothAffineAdditionProjection_inputs]

end FLT.Mazur.WeierstrassIntegralChart
