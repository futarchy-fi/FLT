/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfFamilyCocycleAssembly
public import FLT.Mazur.SchemeFppfFamilyDiagonalAssembly
public import FLT.Mazur.SchemeFppfFamilyLineDescent

/-!
# Independently supplied family line descent data

The input contains line bundles on the original members, original pair
isomorphisms, and only their original diagonal and unequal triple laws.
The assembled geometric datum and its effectiveness are constructed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeFppfFamily
open SchemePicard SchemeGeometricDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] SchemeCoproductModuleGluing.assembled
variable {X : Scheme.{u}} (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X)

/-- Descent data on the original members and their original pair and triple overlaps. -/
structure IndependentLineData where
  /-- The independently supplied line bundle on every member. -/
  obj : ∀ i, LineBundleCat (𝒰.X i)
  /-- Isomorphisms on the original unequal pairs. -/
  overlap : PairIsomorphisms 𝒰 (fun i ↦ (obj i).val)
  /-- Original member diagonal laws. -/
  diagonal : MemberDiagonals 𝒰 (fun i ↦ (obj i).val) overlap
  /-- Original unequal triple cocycles. -/
  cocycle : MemberCocycles 𝒰 (fun i ↦ (obj i).val) overlap

namespace IndependentLineData
variable {𝒰} (D : IndependentLineData 𝒰)

/-- Build the actual family datum, deriving both laws on the assembled overlap. -/
def toFamily : FamilyLineData 𝒰 where
  obj := SchemeCoproductModuleGluing.assembled 𝒰.X (fun i ↦ (D.obj i).val)
  rankOne := SchemeCoproductModuleGluing.assembled_locallyFreeRankOne 𝒰.X _
    (fun i ↦ (D.obj i).property)
  datum := {
    overlap := assembledOverlap 𝒰 _ D.overlap
    diagonal := assembledOverlap_diagonal 𝒰 _ D.overlap D.diagonal
    cocycle := assembledOverlap_cocycle 𝒰 _ D.overlap D.cocycle }

/-- Source assembly is the existing assembly of the independently supplied line bundles. -/
lemma toFamily_source :
    D.toFamily.obj = ((SchemeCoproductModuleGluing.assembleLine 𝒰.X).obj D.obj).val := rfl

/-- The original line member recovery is retained by the constructed family datum. -/
def memberRecovery (i : 𝒰.I₀) :
    (pullback (Limits.Sigma.ι 𝒰.X i)).obj D.toFamily.obj ≅ (D.obj i).val :=
  SchemeCoproductModuleGluing.recovery 𝒰.X (fun j ↦ (D.obj j).val) i

/-- Descend the independent family datum to a line bundle on the base. -/
def descended : LineBundleCat X := (familyLineEquivalence 𝒰).inverse.obj D.toFamily

/-- The effective base line bundle reconstructs the assembled datum. -/
def descendedComparison :
    (familyLineEquivalence 𝒰).functor.obj D.descended ≅ D.toFamily :=
  (familyLineEquivalence 𝒰).counitIso.app D.toFamily

/-- Effectiveness retains each originally supplied module through component recovery. -/
def descendedMemberRecovery (i : 𝒰.I₀) :
    (pullback (𝒰.f i)).obj D.descended.val ≅ (D.obj i).val :=
  (componentRecovery 𝒰 i).app D.toFamily ≪≫ D.memberRecovery i

/-- The member recovery is precisely the established line-bundle assembly recovery. -/
lemma memberRecovery_lineMemberRecovery (i : 𝒰.I₀) :
    (D.memberRecovery i).hom =
      (((SchemeCoproductModuleGluing.lineMemberRecovery 𝒰.X).hom.app D.obj) i).hom := rfl

end IndependentLineData
end FLT.Mazur.SchemeFppfFamily
