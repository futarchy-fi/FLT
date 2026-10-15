/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingRingMap

/-!
# Original punctured branches under explicit coefficient homomorphisms

Express branch naturality using the literal coefficient ring maps, so that
comparisons of truncated graph charts need no implicit algebra replacement.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
open PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (t : R) (s : S) (hs : f t = s)

/-- The original left branch retains every function under explicit coefficient change. -/
theorem ringMap_leftLaurent :
    (leftLaurentMap s).toRingHom.comp (ringMap f t s hs) =
      (coeffMap f).comp (leftLaurentMap t).toRingHom := by
  subst s
  let _ := f.toAlgebra
  change (leftLaurentMap (algebraMap R S t)).toRingHom.comp
    (ringMap (algebraMap R S) t (algebraMap R S t) rfl) = _
  rw [ringMap_eq_coefficientMap]
  exact congrArg AlgHom.toRingHom (leftLaurent_coefficient R S t)

/-- The original inverse-coordinate branch retains all coefficients and nilpotents as well. -/
theorem ringMap_precedingLaurent :
    (precedingLaurentMap S s).toRingHom.comp (ringMap f t s hs) =
      (coeffMap f).comp (precedingLaurentMap R t).toRingHom := by
  subst s
  let _ := f.toAlgebra
  change (precedingLaurentMap S (algebraMap R S t)).toRingHom.comp
    (ringMap (algebraMap R S) t (algebraMap R S t) rfl) = _
  rw [ringMap_eq_coefficientMap]
  exact congrArg AlgHom.toRingHom (precedingLaurent_coefficient R S t)

/-- The left branch square uses precisely the explicit original coefficient morphism. -/
@[reassoc] theorem leftBranchOpen_ringMap :
    leftBranchOpen S s ≫ Spec.map (CommRingCat.ofHom (ringMap f t s hs)) =
      Spec.map (CommRingCat.ofHom (coeffMap f)) ≫ leftBranchOpen R t := by
  rw [leftBranchOpen_eq_spec, leftBranchOpen_eq_spec, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (ringMap_leftLaurent f t s hs))

/-- The incoming branch square preserves the original reciprocal coordinate. -/
@[reassoc] theorem precedingBranch_ringMap :
    precedingBranch S s ≫ Spec.map (CommRingCat.ofHom (ringMap f t s hs)) =
      Spec.map (CommRingCat.ofHom (coeffMap f)) ≫ precedingBranch R t := by
  rw [precedingBranch_eq_spec, precedingBranch_eq_spec, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (ringMap_precedingLaurent f t s hs))

/-- The original right branch is exactly its full Laurent restriction, without inversion. -/
theorem rightBranchOpen_eq_spec (r : R) : rightBranchOpen R r =
    Spec.map (CommRingCat.ofHom
      ((leftLaurentMap r).comp (branchSwapMap r)).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  change leftPunctureToLaurent r (rightToLeftPuncture r
    (algebraMap (ChartRing r) (RightPuncture r) z)) = _
  rw [rightToLeftPuncture_map, leftPunctureToLaurent_map]
  rfl

end FLT.Mazur.PolygonSmoothing
