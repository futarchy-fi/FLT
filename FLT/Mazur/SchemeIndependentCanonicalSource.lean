/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeIndependentCanonicalFamily

/-!
# The canonical independent source recovers the total pullback

Full faithfulness of coproduct restriction lifts the prescribed member
comparisons to a source isomorphism, with its exact member recovery equation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeFppfFamily.IndependentLineData
open SchemePicard SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] SchemeCoproductModuleGluing.assembled
variable {X : Scheme.{u}} (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X)
variable (L : LineBundleCat X)

/-- The canonical source comparison is prescribed on every original member. -/
def canonicalSourceIso :
    (pullback (projection 𝒰)).obj L.val ≅ (canonicalObj 𝒰 L).toFamily.obj :=
  (SchemeCoproductModuleGluing.decompose 𝒰.X).preimageIso
    (Pi.isoMk (fun i ↦ (comparison (Limits.Sigma.ι 𝒰.X i) (projection 𝒰)
      (𝒰.f i) (inclusion_projection 𝒰 i)).app L.val ≪≫
        ((canonicalObj 𝒰 L).memberRecovery i).symm))

/-- Restricting the source comparison gives the prescribed canonical member comparison. -/
@[reassoc]
lemma canonicalSourceIso_recovery (i : 𝒰.I₀) :
    (pullback (Limits.Sigma.ι 𝒰.X i)).map (canonicalSourceIso 𝒰 L).hom ≫
        ((canonicalObj 𝒰 L).memberRecovery i).hom =
      (comparison (Limits.Sigma.ι 𝒰.X i) (projection 𝒰)
        (𝒰.f i) (inclusion_projection 𝒰 i)).hom.app L.val := by
  have h := congrFun ((SchemeCoproductModuleGluing.decompose 𝒰.X).map_preimage
    ((Pi.isoMk (fun j ↦ (comparison (Limits.Sigma.ι 𝒰.X j) (projection 𝒰)
      (𝒰.f j) (inclusion_projection 𝒰 j)).app L.val ≪≫
        ((canonicalObj 𝒰 L).memberRecovery j).symm)).hom)) i
  change (pullback (Limits.Sigma.ι 𝒰.X i)).map (canonicalSourceIso 𝒰 L).hom =
    (comparison (Limits.Sigma.ι 𝒰.X i) (projection 𝒰)
      (𝒰.f i) (inclusion_projection 𝒰 i)).hom.app L.val ≫
        ((canonicalObj 𝒰 L).memberRecovery i).inv at h
  rw [h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end FLT.Mazur.SchemeFppfFamily.IndependentLineData
