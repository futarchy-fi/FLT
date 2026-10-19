/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicInvariantLocallyRinged
public import FLT.Mazur.CyclicCharacteristicInvariantSections
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Principal neighborhoods of the actual invariant quotient

Unit loci of invariant sections are actual orbit opens. Their source inverse
images are the usual scheme basic opens, hence affine whenever the original
source domain is affine. This does not assert that the quotient opens are affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]
local notation "U" => normalizedDisjointSource n
local notation "A" => disjointComparisonArrows n
local notation "src" => disjointComparisonSource n
variable (W : Opens (Orbit n))

/-- The unit locus of an actual invariant regular function. -/
def invariantPrincipal (s : (invariantSheaf n).obj.obj (op W)) : Opens (Orbit n) :=
  (invariantLocallyRingedSpace n).toRingedSpace.basicOpen s

/-- A principal neighborhood stays inside its original section domain. -/
theorem invariantPrincipal_le (s : (invariantSheaf n).obj.obj (op W)) :
    invariantPrincipal n W s ≤ W :=
  RingedSpace.basicOpen_le (ringedSpace n) s

/-- The principal source domain is computed by the original invariant function. -/
theorem pullOpen_invariantPrincipal (s : (invariantSheaf n).obj.obj (op W)) :
    (pullOpen n (invariantPrincipal n W s)).val =
      (U).basicOpen ((invariantInclusion n).hom.app (op W) s) := by
  have h := LocallyRingedSpace.preimage_basicOpen (invariantLocallyRingedProjection n) s
  change (Opens.map (invariantLocallyRingedProjection n).toShHom.hom.base).obj
    (invariantPrincipal n W s) =
      (U).basicOpen ((invariantLocallyRingedProjection n).toShHom.hom.c.app (op W) s)
    at h
  rw [invariantLocallyRingedProjection_toShHom] at h
  exact h

/-- Principal shrinking preserves affine source domains without a quotient scheme assumption. -/
theorem invariantPrincipal_source_affine (hW : IsAffineOpen (pullOpen n W).val)
    (s : (invariantSheaf n).obj.obj (op W)) :
    IsAffineOpen (pullOpen n (invariantPrincipal n W s)).val := by
  rw [pullOpen_invariantPrincipal]
  exact hW.basicOpen _

/-- Finite intersections of these neighborhoods are computed by multiplying functions. -/
theorem invariantPrincipal_mul (s t : (invariantSheaf n).obj.obj (op W)) :
    invariantPrincipal n W (s * t) =
      invariantPrincipal n W s ⊓ invariantPrincipal n W t :=
  RingedSpace.basicOpen_mul (ringedSpace n) s t

/-- The unit section gives the whole original domain. -/
theorem invariantPrincipal_one : invariantPrincipal n W 1 = W :=
  RingedSpace.basicOpen_of_isUnit _ isUnit_one

/-- Positive powers give the same actual neighborhood. -/
theorem invariantPrincipal_pow (s : (invariantSheaf n).obj.obj (op W))
    (k : ℕ) (hn : 0 < k) :
    invariantPrincipal n W (s ^ k) = invariantPrincipal n W s :=
  RingedSpace.basicOpen_pow (ringedSpace n) s k hn

/-- Every such neighborhood is exactly the image of its affine source basic open. -/
theorem invariantPrincipal_image (s : (invariantSheaf n).obj.obj (op W)) :
    projection n '' ((U).basicOpen ((invariantInclusion n).hom.app (op W) s) : Set _) =
      (invariantPrincipal n W s : Set _) := by
  rw [← pullOpen_invariantPrincipal]
  simpa only [pullOpen, Opens.coe_mk] using
    Set.image_preimage_eq (invariantPrincipal n W s : Set _) (projection_surjective n)

end FLT.Mazur.CyclicCharacteristicOrbit
