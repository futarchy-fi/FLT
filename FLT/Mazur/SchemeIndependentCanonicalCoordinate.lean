/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeIndependentCanonicalSource
public import FLT.Mazur.SheafPullbackCoordinateRecoveryNaturality

/-!
# Canonical source comparison along every original coordinate

Further pullback of the source comparison recovers the prescribed
canonical member chart through the assembled coordinate recovery.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeFppfFamily.IndependentLineData
open SchemePicard SheafPullbackPathComparison SheafPullbackCoordinateRecovery
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] SchemeCoproductModuleGluing.assembled
variable {X : Scheme.{u}} (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X)
variable (L : LineBundleCat X)

/-- Every further coordinate retains the canonical member comparison. -/
lemma canonicalSourceIso_coordinate (i : 𝒰.I₀) {T : Scheme.{u}} (t : T ⟶ 𝒰.X i) :
    (pullback (t ≫ Limits.Sigma.ι 𝒰.X i)).map (canonicalSourceIso 𝒰 L).hom ≫
      (recovery t (Limits.Sigma.ι 𝒰.X i) _ rfl (canonicalObj 𝒰 L).toFamily.obj
        ((canonicalObj 𝒰 L).memberRecovery i)).hom =
    (recovery t (Limits.Sigma.ι 𝒰.X i) _ rfl ((pullback (projection 𝒰)).obj L.val)
      ((comparison (Limits.Sigma.ι 𝒰.X i) (projection 𝒰) (𝒰.f i)
        (inclusion_projection 𝒰 i)).app L.val)).hom := by
  have h := recovery_map t (Limits.Sigma.ι 𝒰.X i) _ rfl
    ((comparison (Limits.Sigma.ι 𝒰.X i) (projection 𝒰) (𝒰.f i)
      (inclusion_projection 𝒰 i)).app L.val)
    ((canonicalObj 𝒰 L).memberRecovery i) (canonicalSourceIso 𝒰 L).hom
    (𝟙 ((pullback (𝒰.f i)).obj L.val))
    (by simpa only [Category.comp_id, Iso.app_hom] using canonicalSourceIso_recovery 𝒰 L i)
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using h

end FLT.Mazur.SchemeFppfFamily.IndependentLineData
