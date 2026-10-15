/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstNodeParameterEquiv

/-!
# Original base structure of the retained first-node parameter isomorphism

The node isomorphism preserves the entire original truncated coefficient
map. This makes its inverse usable in flatness and smoothing calculations.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
variable (R : Type) [CommRing R]
local notation "A" => Ring R 1
local notation "S" => Ring R[T;T⁻¹] 1
local notation "t" => C (parameter R 1)
local notation "e" => parameter R[T;T⁻¹] 1
local notation "b" => Spec.map (CommRingCat.ofHom (C : (A) →+* (A)[T;T⁻¹]))
local notation "c" => Spec.map (CommRingCat.ofHom (stageCoefficientMap (C : R →+* R[T;T⁻¹]) 1))

/-- Moving the Laurent parameter preserves every original truncated-base scalar. -/
@[reassoc] theorem firstNodeParameterIso_hom_structure :
    (firstNodeParameterIso R).hom ≫ chartStructure (A)[T;T⁻¹] (t) ≫ (b) =
      chartStructure (S) (e) ≫ (c) := by
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact firstNodeParameterEquiv_originalScalar R a

/-- The inverse node isomorphism retains that same coefficient structure. -/
@[reassoc] theorem firstNodeParameterIso_inv_structure :
    (firstNodeParameterIso R).inv ≫ chartStructure (S) (e) ≫ (c) =
      chartStructure (A)[T;T⁻¹] (t) ≫ (b) := by
  rw [← firstNodeParameterIso_hom_structure, Iso.inv_hom_id_assoc]

end FLT.Mazur.PolygonInfinitesimalStages
