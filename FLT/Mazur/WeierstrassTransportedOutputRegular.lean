/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassTripleInnerOutputRegular

/-!
# Regular output coordinates on transported addition domains

The projection from a transported affine law to its original domain is an open
immersion. Thus every flat restriction preserves its regular output coordinate.
Polynomial domains have normalized output Z equal to one.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- Transport to an affine input overlap is open over the original addition domain. -/
instance affineOverlapAdditionProjection_isOpenImmersion (j k : Fin 3)
    (i : AdditionChartIndex) :
    IsOpenImmersion (affineOverlapAdditionProjection W j k hΔ i) := by
  dsimp [affineOverlapAdditionProjection, Scheme.Cover.pullbackHom]
  infer_instance

/-- Regular output Z survives every flat restriction of a transported affine law. -/
theorem affineOverlapAdditionSpec_z_regular (j k : Fin 3) (i : AdditionChartIndex)
    {X : Scheme.{u}} (f : X ⟶ (affineOverlapAdditionCover W j k hΔ).X i) [Flat f] :
    IsRegular (specSectionHom (f ≫ affineOverlapAdditionSpec W j k hΔ i)
      (coord W (additionChartOutput i) 2)) := by
  have hs : additionChartSpec W i =
      Spec.map (CommRingCat.ofHom (additionChartAlgOutput W i).toRingHom) := by
    cases i <;> rfl
  rw [affineOverlapAdditionSpec, ← Category.assoc, hs, specSectionHom_comp]
  exact additionChart_output_z_regular_sections W i
    (f ≫ affineOverlapAdditionProjection W j k hΔ i)

/-- A morphism to a normalized affine output always has regular Z. -/
theorem affineOutput_z_regular {X : Scheme.{u}} (f : X ⟶ chartScheme W 2) :
    IsRegular (specSectionHom f (coord W 2 2)) := by
  rw [coord_self, map_one]
  exact isRegular_one

/-- Every member of a mixed input addition cover has regular output on a flat source. -/
theorem mixedProductAdditionSpec_z_regular (j k : Fin 3)
    (hj : j = 1 ∨ j = 2) (hk : k = 1 ∨ k = 2) (ha : j = 2 ∨ k = 2)
    (i : (mixedProductAdditionCover W hΔ j k hj hk ha).I₀)
    {X : Scheme.{u}} (f : X ⟶ (mixedProductAdditionCover W hΔ j k hj hk ha).X i)
    [Flat f] : IsRegular (specSectionHom
      (f ≫ mixedProductAdditionSpec W hΔ j k hj hk ha i)
      (coord W (mixedProductAdditionOutput W hΔ j k hj hk ha i) 2)) := by
  rcases i with ⟨b, i⟩
  cases b
  · exact affineOutput_z_regular W _
  · exact affineOverlapAdditionSpec_z_regular W hΔ j k i f

/-- The infinity input cover also has regular output on every flat source. -/
theorem yProductAdditionSpec_z_regular (i : (yProductAdditionCover W hΔ).I₀)
    {X : Scheme.{u}} (f : X ⟶ (yProductAdditionCover W hΔ).X i) [Flat f] :
    IsRegular (specSectionHom (f ≫ yProductAdditionSpec W hΔ i)
      (coord W (yProductAdditionOutput W hΔ i) 2)) := by
  rcases i with ⟨i, t⟩
  cases i with
  | affine => exact affineOverlapAdditionSpec_z_regular W hΔ 1 1 t f
  | polynomial => exact affineOutput_z_regular W _
  | infinity =>
    change IsRegular (specSectionHom
      (f ≫ Spec.map (CommRingCat.ofHom (infinityAdditionChart W).toRingHom)) _)
    rw [specSectionHom_comp]
    exact specSectionHom_isRegular f (infinityAdditionChart_z_regular W)

end FLT.Mazur.WeierstrassIntegralChart
