/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothAffineAddition

/-!
# Integral addition with a smooth first affine input

The second input may be singular. The four actual addition charts already
cover this larger open, so their descended law extends the smooth group law
without a discriminant hypothesis or a smoothness assumption on the output.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The full affine pair open where only the first input is smooth. -/
def leftSmoothAffineInputOpen : (Spec (.of (AffineProduct W))).Opens :=
  Spec.map (CommRingCat.ofHom (productLeft W).toRingHom) ⁻¹ᵁ
    (chartStructure W 2).smoothLocus

/-- A smooth first input suffices for the original four regular formulas to cover. -/
theorem leftSmoothAffineInputOpen_le_domain :
    leftSmoothAffineInputOpen W ≤ affineAdditionDomain W := by
  intro p hp
  apply mem_affineAdditionDomain_of_nonsingular
  exact affineAlgebra_residue_nonsingular_at W (productLeft W) p hp

/-- The larger affine input open maps into the actual domain of the glued partial law. -/
def leftSmoothAffineInputToDomain :
    (leftSmoothAffineInputOpen W).toScheme ⟶ (affineAdditionDomain W).toScheme :=
  IsOpenImmersion.lift (affineAdditionDomain W).ι (leftSmoothAffineInputOpen W).ι (by
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact leftSmoothAffineInputOpen_le_domain W)

/-- The domain lift preserves the original input pair on every function. -/
@[reassoc] theorem leftSmoothAffineInputToDomain_inclusion :
    leftSmoothAffineInputToDomain W ≫ (affineAdditionDomain W).ι =
      (leftSmoothAffineInputOpen W).ι := IsOpenImmersion.lift_fac _ _ _

/-- The integral affine law allows all second inputs, including the singular locus. -/
def leftSmoothAffineAddition :
    (leftSmoothAffineInputOpen W).toScheme ⟶ integralCurve W :=
  leftSmoothAffineInputToDomain W ≫ affinePartialAddition W

/-- This enlarged law is over the original coefficient spectrum. -/
@[reassoc] theorem leftSmoothAffineAddition_structure :
    leftSmoothAffineAddition W ≫ integralCurveStructure W =
      (leftSmoothAffineInputOpen W).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (AffineProduct W))) := by
  rw [leftSmoothAffineAddition, Category.assoc, affinePartialAddition_structure,
    leftSmoothAffineInputToDomain_inclusion_assoc]

/-- The original smooth pair open is contained in the enlarged input domain. -/
def smoothAffineToLeftSmooth :
    (smoothAffineInputOpen W).toScheme ⟶ (leftSmoothAffineInputOpen W).toScheme :=
  (Spec (.of (AffineProduct W))).homOfLE (show smoothAffineInputOpen W ≤
    leftSmoothAffineInputOpen W from inf_le_left)

/-- Inclusion into the enlarged input open retains the original affine coordinates. -/
@[reassoc] theorem smoothAffineToLeftSmooth_inclusion :
    smoothAffineToLeftSmooth W ≫ (leftSmoothAffineInputOpen W).ι =
      (smoothAffineInputOpen W).ι := Scheme.homOfLE_ι _ _

/-- Restriction of the enlarged law is the original smooth group addition. -/
@[reassoc] theorem smoothAffineToLeftSmooth_addition :
    smoothAffineToLeftSmooth W ≫ leftSmoothAffineAddition W =
      smoothAffineAddition W ≫ (integralSmoothOpen W).ι := by
  rw [leftSmoothAffineAddition, smoothAffineAddition_partial, ← Category.assoc]
  congr 1
  apply (cancel_mono (affineAdditionDomain W).ι).mp
  rw [Category.assoc, leftSmoothAffineInputToDomain_inclusion,
    smoothAffineToLeftSmooth_inclusion, smoothAffineInputToDomain_inclusion]

/-- Every original addition chart computes the enlarged law on its actual common inputs. -/
theorem leftSmoothAffineAddition_commonChart (i : AdditionChartIndex) {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothAffineInputOpen W).toScheme)
    (g : X ⟶ Spec (additionChartRing W i))
    (h : f ≫ (leftSmoothAffineInputOpen W).ι = g ≫ additionChartInclusion W i) :
    f ≫ leftSmoothAffineAddition W = g ≫ additionCurveChart W i := by
  have he : f ≫ leftSmoothAffineInputToDomain W = g ≫ additionChartToDomain W i := by
    apply (cancel_mono (affineAdditionDomain W).ι).mp
    simpa only [Category.assoc, leftSmoothAffineInputToDomain_inclusion,
      additionChartToDomain_inclusion] using h
  rw [leftSmoothAffineAddition, ← Category.assoc, he, Category.assoc,
    additionChartToDomain_addition]

/-- The four actual affine formulas cover every pair with smooth first input. -/
def leftSmoothAffineAdditionCover : (leftSmoothAffineInputOpen W).toScheme.OpenCover :=
  (affineAdditionDomainCover W).pullback₁ (leftSmoothAffineInputToDomain W)

/-- Projection to each original affine formula, retaining possibly singular second inputs. -/
def leftSmoothAffineAdditionProjection (i : AdditionChartIndex) :
    (leftSmoothAffineAdditionCover W).X i ⟶ Spec (additionChartRing W i) :=
  (affineAdditionDomainCover W).pullbackHom (leftSmoothAffineInputToDomain W) i

/-- Each covering chart retains its actual pair of affine inputs. -/
@[reassoc] theorem leftSmoothAffineAdditionProjection_inputs (i : AdditionChartIndex) :
    leftSmoothAffineAdditionProjection W i ≫ additionChartInclusion W i =
      (leftSmoothAffineAdditionCover W).f i ≫ (leftSmoothAffineInputOpen W).ι := by
  rw [← additionChartToDomain_inclusion, ← Category.assoc]
  change ((affineAdditionDomainCover W).pullbackHom _ i ≫
    (affineAdditionDomainCover W).f i) ≫ _ = _
  rw [Scheme.Cover.pullbackHom_map, Category.assoc,
    leftSmoothAffineInputToDomain_inclusion]
  rfl

/-- The enlarged law retains every original formula on its actual covering domain. -/
@[reassoc] theorem leftSmoothAffineAdditionProjection_addition (i : AdditionChartIndex) :
    leftSmoothAffineAdditionProjection W i ≫ additionCurveChart W i =
      (leftSmoothAffineAdditionCover W).f i ≫ leftSmoothAffineAddition W :=
  (leftSmoothAffineAddition_commonChart W i _ _
    (leftSmoothAffineAdditionProjection_inputs W i).symm).symm

end FLT.Mazur.WeierstrassIntegralChart
