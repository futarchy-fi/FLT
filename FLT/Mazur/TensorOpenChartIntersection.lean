/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.TensorOpenChartOverlap
public import FLT.Mazur.TensorOpenChartRange

/-!
# Exact principal intersections after tensor coefficient extension

An exact original principal intersection remains exact in the actual tensor
atlas. Together with the original gluing equality this proves a cartesian
square, without discarding any components of either tensor algebra.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.TensorOpenChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
  {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
  (i : Spec (.of A) ⟶ X) (j : Spec (.of B) ⟶ X)
  (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))
  (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B)))
  (x : A) (y : B) (e : Localization.Away x ≃ₐ[R] Localization.Away y)

/-- Inverse images between tensor charts retain the whole original intersection. -/
theorem chart_preimage_range :
    chart (S := S) f j hj ⁻¹' Set.range (chart (S := S) f i hi) =
      projection ⁻¹' (j ⁻¹' Set.range i) := by
  rw [chart_range]
  ext z
  change pullback.snd _ f (chart f j hj z) ∈ Set.range i ↔ _
  rw [← Scheme.Hom.comp_apply, chart_snd]
  rfl

/-- An exact original principal intersection stays the full tensor principal open. -/
theorem chart_principal_preimage
    (h : j ⁻¹' Set.range i = Set.range
      (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away y))))) :
    chart (S := S) f j hj ⁻¹' Set.range (chart (S := S) f i hi) =
      Set.range (PrincipalOpenTensor.inclusion S y) := by
  rw [chart_preimage_range, h]
  change projection ⁻¹' Set.range
    (PrimeSpectrum.comap (algebraMap B (Localization.Away y))) =
      Set.range (PrimeSpectrum.comap
        (algebraMap (S ⊗[R] B) (Localization.Away ((1 : S) ⊗ₜ[R] y))))
  rw [PrimeSpectrum.localization_away_comap_range _ y,
    PrimeSpectrum.localization_away_comap_range _ ((1 : S) ⊗ₜ[R] y)]
  rfl

variable [IsOpenImmersion i]

/-- The original exact principal overlap yields the full cartesian tensor intersection. -/
theorem chart_overlap_isPullback
    (h : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away x))) ≫ i =
        Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away y))) ≫ j)
    (hp : j ⁻¹' Set.range i = Set.range
      (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away y))))) :
    IsPullback ((PrincipalOpenTensor.transitionIso S x y e).hom ≫
      PrincipalOpenTensor.inclusion S x) (PrincipalOpenTensor.inclusion S y)
      (chart (S := S) f i hi) (chart (S := S) f j hj) := by
  apply IsOpenImmersion.isPullback
  · exact (Category.assoc _ _ _).trans (chart_overlap S f i j hi hj x y e h) |>.symm
  · exact TopologicalSpace.Opens.ext (chart_principal_preimage S f i j hi hj y hp)

end FLT.Mazur.TensorOpenChart
