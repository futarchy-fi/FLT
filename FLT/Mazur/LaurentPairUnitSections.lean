/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalUniversalEdges

/-!
# The two full unit sections of the double Laurent scheme

Setting either variable to one retains the entire other Laurent coordinate
over an arbitrary coefficient ring, including all its nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentPairUnitSections
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
universe u
variable (R : Type u) [CommRing R]
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹]))
local notation "p" => Spec.map (CommRingCat.ofHom
  (algebraMap R[T;T⁻¹] R[T;T⁻¹][T;T⁻¹]))
local notation "q" => Spec.map (CommRingCat.ofHom
  (PolygonScalingNaturality.coeffMap (LaurentPolynomial.C : R →+* R[T;T⁻¹])))

/-- Set the first, coefficient Laurent variable to one. -/
def firstUnit : branchTorus R ⟶ branchTorus R[T;T⁻¹] :=
  Spec.map (CommRingCat.ofHom (PolygonScalingNaturality.coeffMap
    (LaurentUnitPoints.evalUnit (R := R) (1 : Rˣ)).toRingHom))

/-- Set the second, outer Laurent variable to one. -/
def secondUnit : branchTorus R ⟶ branchTorus R[T;T⁻¹] :=
  markedTorusSection (1 : R[T;T⁻¹]ˣ)

/-- The first coordinate of the first unit section is the original unit marking. -/
@[reassoc] theorem firstUnit_fst :
    firstUnit R ≫ (p) = (b) ≫ markedTorusSection (1 : Rˣ) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact PolygonScalingNaturality.coeffMap_C _ z

/-- The first unit section leaves the entire second Laurent coordinate unchanged. -/
@[reassoc] theorem firstUnit_snd : firstUnit R ≫ (q) = 𝟙 _ := by
  change Spec.map _ ≫ Spec.map _ = 𝟙 (Spec (.of R[T;T⁻¹]))
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  apply PolygonScalingNaturality.ringHom_ext <;>
    simp [CommRingCat.hom_comp, CommRingCat.hom_id, LaurentUnitPoints.evalUnit]

/-- The second unit section leaves the entire first Laurent coordinate unchanged. -/
@[reassoc] theorem secondUnit_fst : secondUnit R ≫ (p) = 𝟙 _ := by
  change Spec.map _ ≫ Spec.map _ = 𝟙 (Spec (.of R[T;T⁻¹]))
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  exact (LaurentUnitPoints.evalUnit (R := R[T;T⁻¹]) (1 : R[T;T⁻¹]ˣ)).comp_algebraMap

/-- The second coordinate of the second unit section is the original unit marking. -/
@[reassoc] theorem secondUnit_snd :
    secondUnit R ≫ (q) = (b) ≫ markedTorusSection (1 : Rˣ) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply PolygonScalingNaturality.ringHom_ext <;>
    simp [CommRingCat.hom_comp, LaurentUnitPoints.evalUnit]

end FLT.Mazur.LaurentPairUnitSections
