/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfFamilyCover
public import FLT.Mazur.SchemeFppfLineDescentEquivalence

/-!
# Line descent for an fppf family in coproduct coordinates

Descent data live on the actual coproduct and its actual double and triple
fiber products. The equivalence retains recovery on every original member.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeFppfFamily
open SchemePicard SchemeGeometricDescent SchemeAffineDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X)

/-- Family descent data, expressed on the disjoint union of all its members. -/
abbrev FamilyLineData := LineData (projection 𝒰)

/-- Effective descent for an arbitrary small fppf family in coproduct coordinates. -/
def familyLineEquivalence : LineBundleCat X ≌ FamilyLineData 𝒰 :=
  lineDescentEquivalence (projection 𝒰)

/-- Restriction of the original source sheaf to a member of the family. -/
def component (i : 𝒰.I₀) : FamilyLineData 𝒰 ⥤ (𝒰.X i).Modules :=
  LineData.forget (projection 𝒰) ⋙ pullback (Limits.Sigma.ι 𝒰.X i)

/-- Canonical family descent restricts to ordinary pullback along each original map. -/
def canonicalComponent (i : 𝒰.I₀) :
    (familyLineEquivalence 𝒰).functor ⋙ component 𝒰 i ≅
      lineBundleForget X ⋙ pullback (𝒰.f i) :=
  Functor.isoWhiskerLeft (lineBundleForget X)
    (pullbackComp (Limits.Sigma.ι 𝒰.X i) (projection 𝒰) ≪≫
      pullbackCongr (inclusion_projection 𝒰 i))

/-- Gluing recovers the original sheaf on each member, naturally in the descent datum. -/
def componentRecovery (i : 𝒰.I₀) :
    (familyLineEquivalence 𝒰).inverse ⋙ lineBundleForget X ⋙ pullback (𝒰.f i) ≅
      component 𝒰 i :=
  Functor.isoWhiskerLeft (familyLineEquivalence 𝒰).inverse
      (canonicalComponent 𝒰 i).symm ≪≫
    Functor.isoWhiskerRight (familyLineEquivalence 𝒰).counitIso (component 𝒰 i)

/-- Every family datum is recovered from a line bundle on the base. -/
lemma family_effective (D : FamilyLineData 𝒰) :
    ∃ L : LineBundleCat X, Nonempty ((familyLineEquivalence 𝒰).functor.obj L ≅ D) :=
  ⟨(familyLineEquivalence 𝒰).inverse.obj D,
    ⟨(familyLineEquivalence 𝒰).counitIso.app D⟩⟩

end FLT.Mazur.SchemeFppfFamily
