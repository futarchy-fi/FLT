/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentDomainPairUnits
public import FLT.Mazur.LaurentSchemeCoordinates

/-!
# Uniqueness of normalized morphisms on the double torus

Over a domain, a morphism from the double torus to the torus whose two
identity slices are the identity is unique. This concerns the actual scheme
morphism, without assuming a multiplication or a homomorphism property.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentNormalizedMorphism
open LaurentSchemeCoordinates LaurentPairUnitSections
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
local notation "L" => R[T;T⁻¹]
local notation "D" => R[T;T⁻¹][T;T⁻¹]
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap R L))
local notation "p" => Spec.map (CommRingCat.ofHom (algebraMap L D))

/-- A normalized scheme map has exactly the product Laurent coordinate. -/
theorem coordinate_eq_product (f : Spec (.of D) ⟶ Spec (.of L))
    (hf : f ≫ (b) = Spec.map (CommRingCat.ofHom (algebraMap R D)))
    (h₁ : firstUnit R ≫ f = 𝟙 _) (h₂ : secondUnit R ≫ f = 𝟙 _) :
    coordinate f hf = Units.map (LaurentPolynomial.C : L →+* D)
      (PolygonUniversalScaling.u (R := R)) * PolygonUniversalScaling.u := by
  apply LaurentDomainPairUnits.eq_product
  · apply Units.ext
    have he : CommRingCat.ofHom (algebraHom f hf).toRingHom ≫
        CommRingCat.ofHom (PolygonScalingNaturality.coeffMap
          (LaurentUnitPoints.evalUnit (R := R) (1 : Rˣ)).toRingHom) = 𝟙 _ := by
      apply Spec.map_injective
      rw [Spec.map_comp, algebraHom_spec, Spec.map_id]
      exact h₁
    simpa [coordinate, LaurentUnitPoints.pointUnit, PolygonUniversalScaling.u,
      PolygonChartScaling.coordinateUnit] using
      congrArg (fun g : CommRingCat.of L ⟶ CommRingCat.of L ↦
        g.hom (LaurentPolynomial.T 1)) he
  · apply Units.ext
    have he : CommRingCat.ofHom (algebraHom f hf).toRingHom ≫
        CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := L) (1 : Lˣ)).toRingHom =
          𝟙 _ := by
      apply Spec.map_injective
      rw [Spec.map_comp, algebraHom_spec, Spec.map_id]
      exact h₂
    simpa [coordinate, LaurentUnitPoints.pointUnit, PolygonUniversalScaling.u,
      PolygonChartScaling.coordinateUnit] using
      congrArg (fun g : CommRingCat.of L ⟶ CommRingCat.of L ↦
        g.hom (LaurentPolynomial.T 1)) he

/-- The two unit laws determine an actual double-torus morphism over a domain. -/
theorem hom_ext (f g : Spec (.of D) ⟶ Spec (.of L))
    (hf : f ≫ (b) = Spec.map (CommRingCat.ofHom (algebraMap R D)))
    (hg : g ≫ (b) = Spec.map (CommRingCat.ofHom (algebraMap R D)))
    (hf₁ : firstUnit R ≫ f = 𝟙 _) (hf₂ : secondUnit R ≫ f = 𝟙 _)
    (hg₁ : firstUnit R ≫ g = 𝟙 _) (hg₂ : secondUnit R ≫ g = 𝟙 _) : f = g := by
  apply LaurentSchemeCoordinates.ext f hf g hg
  rw [coordinate_eq_product f hf hf₁ hf₂, coordinate_eq_product g hg hg₁ hg₂]

end FLT.Mazur.LaurentNormalizedMorphism
