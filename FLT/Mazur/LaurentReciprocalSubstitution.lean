/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentUnitPoints
public import FLT.Mazur.PolygonSmoothingRingMapBranch

/-!
# Full reciprocal substitution on the punctured node

Conjugating an arbitrary Laurent unit substitution by coordinate inversion
produces its reciprocal unit. The result holds on every Laurent function and
on the full right punctured node, over an arbitrary coefficient ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentUnitPoints
open LaurentPolynomial PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (u : R[T;T⁻¹]ˣ)

/-- Reciprocal substitution followed by inversion is inversion followed by substitution. -/
theorem evalUnit_reciprocal_invert :
    (evalUnit (Units.map invert.toMonoidHom u⁻¹)).comp invert.toAlgHom =
      invert.toAlgHom.comp (evalUnit u) := by
  apply hom_ext <;> simp [Units.map]

/-- The entire Laurent morphism commutes with reciprocal input and output coordinates. -/
@[reassoc] theorem spec_evalUnit_reciprocal_invert :
    (edgeInversion R).hom ≫ Spec.map (CommRingCat.ofHom (evalUnit u).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (evalUnit (Units.map invert.toMonoidHom u⁻¹)).toRingHom) ≫
          (edgeInversion R).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext
    (congrArg AlgHom.toRingHom (evalUnit_reciprocal_invert u)).symm)

/-- Inverting the original edge coordinate twice is the identity on the whole torus. -/
theorem edgeInversion_comp_self : (edgeInversion R).hom ≫ (edgeInversion R).hom = 𝟙 _ := by
  change Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact involutive_invert

/-- The inverse parameterization of the incoming edge is the original right puncture. -/
@[reassoc] theorem edgeInversion_preceding (t : R) :
    (edgeInversion R).hom ≫ precedingBranch R t = rightBranchOpen R t := by
  rw [precedingBranch, ← Category.assoc, edgeInversion_comp_self, Category.id_comp]

/-- Reciprocal substitution has the exact original incoming node target on all functions. -/
@[reassoc] theorem spec_evalUnit_incoming (t : R) :
    (edgeInversion R).hom ≫ Spec.map (CommRingCat.ofHom (evalUnit u).toRingHom) ≫
        precedingBranch R t =
      Spec.map (CommRingCat.ofHom
        (evalUnit (Units.map invert.toMonoidHom u⁻¹)).toRingHom) ≫ rightBranchOpen R t := by
  rw [← Category.assoc, spec_evalUnit_reciprocal_invert, Category.assoc,
    edgeInversion_preceding]

end FLT.Mazur.LaurentUnitPoints
