/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentCoefficientEvaluation
public import FLT.Mazur.LaurentPairUnitSections

/-!
# Both Laurent pair projections commute with coefficient change

These are equations on the full affine schemes, over arbitrary coefficient
rings. They retain both independent Laurent variables and all nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentPairCoefficientNaturality
open PolygonScalingNaturality
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- The coefficient Laurent variable commutes with double coefficient change. -/
theorem firstProjection_ring :
    (coeffMap (coeffMap f)).comp
        (LaurentPolynomial.C : R[T;T⁻¹] →+* R[T;T⁻¹][T;T⁻¹]) =
      (LaurentPolynomial.C : S[T;T⁻¹] →+* S[T;T⁻¹][T;T⁻¹]).comp (coeffMap f) := by
  apply RingHom.ext
  intro p
  exact coeffMap_C (coeffMap f) p

/-- The outer Laurent variable commutes with double coefficient change. -/
theorem secondProjection_ring :
    (coeffMap (coeffMap f)).comp
        (coeffMap (LaurentPolynomial.C : R →+* R[T;T⁻¹])) =
      (coeffMap (LaurentPolynomial.C : S →+* S[T;T⁻¹])).comp (coeffMap f) := by
  rw [← coeffMap_comp, ← coeffMap_comp]
  congr 1
  apply RingHom.ext
  intro r
  exact coeffMap_C f r

/-- The first full Laurent pair projection is natural under coefficient change. -/
@[reassoc] theorem firstProjection_spec :
    Spec.map (CommRingCat.ofHom (coeffMap (coeffMap f))) ≫
        Spec.map (CommRingCat.ofHom
          (LaurentPolynomial.C : R[T;T⁻¹] →+* R[T;T⁻¹][T;T⁻¹])) =
      Spec.map (CommRingCat.ofHom
        (LaurentPolynomial.C : S[T;T⁻¹] →+* S[T;T⁻¹][T;T⁻¹])) ≫
        Spec.map (CommRingCat.ofHom (coeffMap f)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun g ↦ Spec.map (CommRingCat.ofHom g)) (firstProjection_ring f)

/-- The second full Laurent pair projection is natural under coefficient change. -/
@[reassoc] theorem secondProjection_spec :
    Spec.map (CommRingCat.ofHom (coeffMap (coeffMap f))) ≫
        Spec.map (CommRingCat.ofHom (coeffMap (LaurentPolynomial.C : R →+* R[T;T⁻¹]))) =
      Spec.map (CommRingCat.ofHom (coeffMap (LaurentPolynomial.C : S →+* S[T;T⁻¹]))) ≫
        Spec.map (CommRingCat.ofHom (coeffMap f)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun g ↦ Spec.map (CommRingCat.ofHom g)) (secondProjection_ring f)

end FLT.Mazur.LaurentPairCoefficientNaturality
