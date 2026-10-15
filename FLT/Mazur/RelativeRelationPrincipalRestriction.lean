/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationInvariantPrincipal
public import FLT.Mazur.RelativeRelationClosedSections

/-!
# Principal restriction on the original source and quotient

The actual source section ring on an invariant principal open is a
localization. Principal neighborhoods also commute with the whole descended
locally ringed map, including closed boundaries and infinitesimal transitions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q) (W : Opens (Orbit e))
  (s : (invariantSheaf e).obj.obj (op W))
local notation "D" => invariantPrincipal e W s
local notation "j" => homOfLE (invariantPrincipal_le e W s)

/-- Restriction to the actual invariant principal neighborhood. -/
def principalRestriction : (invariantSheaf e).obj.obj (op W) →+*
    (invariantSheaf e).obj.obj (op D) :=
  ((invariantSheaf e).obj.map (j).op).hom

/-- Restriction of original source functions to that same neighborhood. -/
def principalSourceRestriction : (sourceSheaf e).obj.obj (op W) →+*
    (sourceSheaf e).obj.obj (op D) :=
  ((sourceSheaf e).obj.map (j).op).hom

/-- The invariant restriction uses exactly the original source restriction. -/
theorem principalRestriction_inclusion (a : (invariantSheaf e).obj.obj (op W)) :
    (invariantInclusion e).hom.app (op D) (principalRestriction e W s a) =
      principalSourceRestriction e W s ((invariantInclusion e).hom.app (op W) a) :=
  congrArg (fun k ↦ k a) ((invariantInclusion e).hom.naturality (j).op)

/-- The defining function becomes invertible on the principal neighborhood. -/
theorem principalRestriction_isUnit : IsUnit (principalRestriction e W s s) :=
  RingedSpace.isUnit_res_basicOpen (ringedSpace e) s

/-- The source section ring is the localization at the actual original invariant function. -/
theorem principalSourceRestriction_isLocalization (hW : IsAffineOpen (pullOpen e W).val) :
    @IsLocalization.Away _ _ ((invariantInclusion e).hom.app (op W) s)
      ((sourceSheaf e).obj.obj (op D)) _ (principalSourceRestriction e W s).toAlgebra := by
  exact hW.isLocalization_of_eq_basicOpen _ _ (pullOpen_invariantPrincipal e W s)

variable {S' : Scheme.{u}} {A' U' : Over S'} {p' q' : A' ⟶ U'}
  (e' : CategoryTheory.EquivalenceRelation p' q')
  (g : U'.left ⟶ U.left) (r : A'.left ⟶ A.left)
  (hp : r ≫ p.left = p'.left ≫ g) (hq : r ≫ q.left = q'.left ≫ g)
local notation "m" => invariantMap e e' g r hp hq

/-- The whole original map pulls principal opens back to loci of pulled-back functions. -/
theorem invariantMap_principal :
    (Opens.map (m).base).obj D =
      invariantPrincipal e' ((Opens.map (m).base).obj W) ((m).c.app (op W) s) :=
  LocallyRingedSpace.preimage_basicOpen m s

/-- Closed restriction preserves the affine source domains of these compatible neighborhoods. -/
theorem invariantMap_principal_source_affine [IsClosedImmersion g]
    (hW : IsAffineOpen (pullOpen e W).val) :
    IsAffineOpen (pullOpen e' ((Opens.map (m).base).obj D)).val := by
  rw [invariantMap_sourceOpen_eq]
  exact (invariantPrincipal_source_affine e W hW s).preimage g

end FLT.Mazur.RelativeRelationOrbit
