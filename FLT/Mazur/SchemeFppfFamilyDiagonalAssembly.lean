/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfFamilyMemberOverlap
public import FLT.Mazur.SchemeOverlapDiagonalSourceIso
public import FLT.Mazur.SchemeOverlapRefinementDiagonalDetection
public import FLT.Mazur.SchemeGeometricDescentData

/-!
# The assembled family overlap satisfies the original diagonal laws

Only equations on the original members are supplied. Recovery and detection
on the coproduct cover prove the diagonal equation for the assembled overlap.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeFppfFamily
open SchemeOverlapRefinement SchemeOverlapDiagonalChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] SchemeCoproductModuleGluing.assembled
variable {X : Scheme.{u}} (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X)
variable (M : ∀ i, (𝒰.X i).Modules) (e : PairIsomorphisms 𝒰 M)

/-- The supplied diagonal equations live on the original member schemes. -/
def MemberDiagonals : Prop := ∀ i,
  SchemeGeometricDescent.Diagonal (𝒰.f i) (M i) (e (i, i))

/-- Original diagonal laws hold after refining the assembled overlap to any member. -/
lemma refined_member_diagonal (he : MemberDiagonals 𝒰 M e) (i : 𝒰.I₀) :
    SchemeGeometricDescent.Diagonal (𝒰.f i)
      ((pullback (Limits.Sigma.ι 𝒰.X i)).obj (SchemeCoproductModuleGluing.assembled 𝒰.X M))
      (refine (projection 𝒰) (𝒰.f i) (𝟙 X) (Limits.Sigma.ι 𝒰.X i)
        (member_square 𝒰 i) (assembledOverlap 𝒰 M e)) :=
  diagonal_of_sourceIso _ _ _ _ _ (SchemeCoproductModuleGluing.recovery 𝒰.X M i)
    _ (e (i, i)) (refined_member_overlap 𝒰 M e i) (he i)

/-- The actual assembled overlap satisfies the diagonal law from the original members. -/
lemma assembledOverlap_diagonal (he : MemberDiagonals 𝒰 M e) :
    SchemeGeometricDescent.Diagonal (projection 𝒰)
      (SchemeCoproductModuleGluing.assembled 𝒰.X M) (assembledOverlap 𝒰 M e) := by
  apply ModuleSheafOpenImmersionGluing.hom_ext 𝒰.X (Limits.Sigma.ι 𝒰.X)
    (fun x ↦ (sigmaOpenCover 𝒰.X).exists_eq x)
  intro i
  exact diagonal_pullback_of_refine (projection 𝒰) (𝒰.f i) (𝟙 X)
    (Limits.Sigma.ι 𝒰.X i) (member_square 𝒰 i)
    (SchemeCoproductModuleGluing.assembled 𝒰.X M) (assembledOverlap 𝒰 M e)
    (refined_member_diagonal 𝒰 M e he i)

end FLT.Mazur.SchemeFppfFamily
