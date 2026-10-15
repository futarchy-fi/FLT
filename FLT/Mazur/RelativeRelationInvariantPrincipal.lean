/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationInvariantLocallyRinged
public import FLT.Mazur.RelativeRelationInvariantSections
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Principal neighborhoods of the actual invariant quotient

Unit loci of invariant sections are actual orbit opens. Their source inverse
images are the usual scheme basic opens, hence affine whenever the original
source domain is affine. This does not assert that the quotient opens are affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q) (W : Opens (Orbit e))

/-- The unit locus of an actual invariant regular function. -/
def invariantPrincipal (s : (invariantSheaf e).obj.obj (op W)) : Opens (Orbit e) :=
  (invariantLocallyRingedSpace e).toRingedSpace.basicOpen s

/-- A principal neighborhood stays inside its original section domain. -/
theorem invariantPrincipal_le (s : (invariantSheaf e).obj.obj (op W)) :
    invariantPrincipal e W s ≤ W :=
  RingedSpace.basicOpen_le (ringedSpace e) s

/-- The principal source domain is computed by the original invariant function. -/
theorem pullOpen_invariantPrincipal (s : (invariantSheaf e).obj.obj (op W)) :
    (pullOpen e (invariantPrincipal e W s)).val =
      U.left.basicOpen ((invariantInclusion e).hom.app (op W) s) := by
  have h := LocallyRingedSpace.preimage_basicOpen (invariantLocallyRingedProjection e) s
  change (Opens.map (invariantLocallyRingedProjection e).toShHom.hom.base).obj
    (invariantPrincipal e W s) =
      U.left.basicOpen ((invariantLocallyRingedProjection e).toShHom.hom.c.app (op W) s)
    at h
  rw [invariantLocallyRingedProjection_toShHom] at h
  exact h

/-- Principal shrinking preserves affine source domains without a quotient scheme assumption. -/
theorem invariantPrincipal_source_affine (hW : IsAffineOpen (pullOpen e W).val)
    (s : (invariantSheaf e).obj.obj (op W)) :
    IsAffineOpen (pullOpen e (invariantPrincipal e W s)).val := by
  rw [pullOpen_invariantPrincipal]
  exact hW.basicOpen _

/-- Finite intersections of these neighborhoods are computed by multiplying functions. -/
theorem invariantPrincipal_mul (s t : (invariantSheaf e).obj.obj (op W)) :
    invariantPrincipal e W (s * t) =
      invariantPrincipal e W s ⊓ invariantPrincipal e W t :=
  RingedSpace.basicOpen_mul (ringedSpace e) s t

/-- The unit section gives the whole original domain. -/
theorem invariantPrincipal_one : invariantPrincipal e W 1 = W :=
  RingedSpace.basicOpen_of_isUnit _ isUnit_one

/-- Positive powers give the same actual neighborhood. -/
theorem invariantPrincipal_pow (s : (invariantSheaf e).obj.obj (op W))
    (n : ℕ) (hn : 0 < n) :
    invariantPrincipal e W (s ^ n) = invariantPrincipal e W s :=
  RingedSpace.basicOpen_pow (ringedSpace e) s n hn

/-- Every such neighborhood is exactly the image of its affine source basic open. -/
theorem invariantPrincipal_image (s : (invariantSheaf e).obj.obj (op W)) :
    projection e '' (U.left.basicOpen ((invariantInclusion e).hom.app (op W) s) : Set _) =
      (invariantPrincipal e W s : Set _) := by
  rw [← pullOpen_invariantPrincipal]
  simpa only [pullOpen, Opens.coe_mk] using
    Set.image_preimage_eq (invariantPrincipal e W s : Set _) (projection_surjective e)

end FLT.Mazur.RelativeRelationOrbit
