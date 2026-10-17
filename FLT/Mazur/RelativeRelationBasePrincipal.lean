/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationInvariantPrincipal

/-!
# Original invariant principal opens from base functions

Pullback from the unchanged relative base constructs actual invariant sections
on every orbit domain. Their unit loci are exactly the intersections with the
base principal preimages; no affine quotient or principal basis is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (W : Opens (Orbit e))
local notation "b" => invariantLocallyRingedBaseMap e

/-- Pullback of a global base function, restricted to the original orbit domain. -/
def invariantBaseSection : Γ(S, ⊤) →+* (invariantSheaf e).obj.obj (op W) :=
  ((invariantSheaf e).obj.map (homOfLE
    (show W ≤ (Opens.map (b).base).obj ⊤ from fun _ _ ↦ trivial)).op).hom.comp
      ((b).c.app (op ⊤)).hom

/-- The actual principal domain of a pulled-back base section. -/
theorem invariantPrincipal_baseSection (r : Γ(S, ⊤)) :
    invariantPrincipal e W (invariantBaseSection e W r) =
      W ⊓ (Opens.map (b).base).obj (S.basicOpen r) := by
  exact (RingedSpace.basicOpen_res (invariantLocallyRingedSpace e).toRingedSpace
    (homOfLE (show W ≤ (Opens.map (b).base).obj ⊤ from fun _ _ ↦ trivial)).op
    ((b).c.app (op ⊤) r)).trans
      (congrArg (W ⊓ ·) (LocallyRingedSpace.preimage_basicOpen (b) r).symm)

/-- The locally ringed base map keeps the original structural map on source points. -/
theorem invariantBaseMap_projection (x : A.left) :
    (b).base (projection e x) = A.hom x := by
  have h := congrArg (fun g ↦ g.base x) (invariantLocallyRingedProjection_baseMap e)
  rw [LocallyRingedSpace.comp_base, invariantLocallyRingedProjection_base] at h
  exact h

/-- Testing a base scalar at an original source point uses the original base function. -/
theorem projection_mem_baseSection (r : Γ(S, ⊤)) (x : A.left) :
    projection e x ∈ invariantPrincipal e W (invariantBaseSection e W r) ↔
      projection e x ∈ W ∧ A.hom x ∈ S.basicOpen r := by
  rw [invariantPrincipal_baseSection]
  change (_ ∧ (b).base (projection e x) ∈ S.basicOpen r) ↔ _
  rw [invariantBaseMap_projection]
  rfl

/-- These original scalar neighborhoods restrict with the prescribed orbit domain. -/
theorem invariantBaseSection_restrict {W' : Opens (Orbit e)} (h : W' ≤ W)
    (r : Γ(S, ⊤)) :
    (invariantSheaf e).obj.map (homOfLE h).op (invariantBaseSection e W r) =
      invariantBaseSection e W' r := by
  change ((invariantSheaf e).obj.map _ ≫ (invariantSheaf e).obj.map _) _ = _
  rw [← Functor.map_comp]
  rfl

end FLT.Mazur.RelativeRelationOrbit
