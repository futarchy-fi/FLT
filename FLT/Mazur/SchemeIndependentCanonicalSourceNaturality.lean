/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeIndependentCanonicalCompatibility

/-!
# Naturality of the canonical source comparison

The prescribed member recovery equations detect naturality on the coproduct.
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

/-- The original source isomorphisms commute with every base line bundle map. -/
@[reassoc]
lemma canonicalSourceIso_naturality {L K : LineBundleCat X} (a : L ⟶ K) :
    (pullback (projection 𝒰)).map a.hom ≫ (canonicalSourceIso 𝒰 K).hom =
      (canonicalSourceIso 𝒰 L).hom ≫ (assemble.map ((canonical 𝒰).map a)).val := by
  apply (SchemeCoproductModuleGluing.decompose 𝒰.X).map_injective
  funext i
  change (pullback (Limits.Sigma.ι 𝒰.X i)).map _ =
    (pullback (Limits.Sigma.ι 𝒰.X i)).map _
  apply (cancel_mono ((canonicalObj 𝒰 K).memberRecovery i).hom).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [canonicalSourceIso_recovery]
  have hr := SchemeCoproductModuleGluing.map_recovery 𝒰.X
    ((canonical 𝒰).map a).val i
  change (pullback (Limits.Sigma.ι 𝒰.X i)).map
      (assemble.map ((canonical 𝒰).map a)).val ≫
        ((canonicalObj 𝒰 K).memberRecovery i).hom =
      ((canonicalObj 𝒰 L).memberRecovery i).hom ≫ (pullback (𝒰.f i)).map a.hom at hr
  rw [hr, ← Category.assoc, canonicalSourceIso_recovery]
  exact (comparison (Limits.Sigma.ι 𝒰.X i) (projection 𝒰)
    (𝒰.f i) (inclusion_projection 𝒰 i)).hom.naturality a.hom

end FLT.Mazur.SchemeFppfFamily.IndependentLineData
