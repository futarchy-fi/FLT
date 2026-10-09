/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfFamilyPairNormalization
public import FLT.Mazur.SheafPullbackCoordinateRecoveryNaturality

/-!
# Original pair recoveries preserve assembled source maps

The left and right pair recovery squares are natural for maps assembled
from independently supplied component maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeFppfFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] SchemeCoproductModuleGluing.assembled
variable {X : Scheme.{u}} (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X)
variable {M N : ∀ i, (𝒰.X i).Modules} (f : ∀ i, M i ⟶ N i)

/-- The original left pair recovery retains each assembled component map. -/
@[reassoc]
lemma pairLeftRecovery_map (ij : 𝒰.I₀ × 𝒰.I₀) :
    (pullback (pairMap 𝒰 ij)).map
        ((pullback (Limits.pullback.fst (projection 𝒰) (projection 𝒰))).map
          (SchemeCoproductModuleGluing.map 𝒰.X f)) ≫ (pairLeftRecovery 𝒰 N ij).hom =
      (pairLeftRecovery 𝒰 M ij).hom ≫
        (pullback (Limits.pullback.fst (𝒰.f ij.1) (𝒰.f ij.2))).map (f ij.1) := by
  rw [pairLeftRecovery_coordinate, pairLeftRecovery_coordinate]
  exact SheafPullbackCoordinateRecovery.comparison_recovery_map _ _ _ _ _
    (pairMap_fst 𝒰 ij) rfl _ _ _ _ (SchemeCoproductModuleGluing.map_recovery 𝒰.X f ij.1)

/-- The original right pair recovery retains each assembled component map. -/
@[reassoc]
lemma pairRightRecovery_map (ij : 𝒰.I₀ × 𝒰.I₀) :
    (pullback (pairMap 𝒰 ij)).map
        ((pullback (Limits.pullback.snd (projection 𝒰) (projection 𝒰))).map
          (SchemeCoproductModuleGluing.map 𝒰.X f)) ≫ (pairRightRecovery 𝒰 N ij).hom =
      (pairRightRecovery 𝒰 M ij).hom ≫
        (pullback (Limits.pullback.snd (𝒰.f ij.1) (𝒰.f ij.2))).map (f ij.2) := by
  rw [pairRightRecovery_coordinate, pairRightRecovery_coordinate]
  exact SheafPullbackCoordinateRecovery.comparison_recovery_map _ _ _ _ _
    (pairMap_snd 𝒰 ij) rfl _ _ _ _ (SchemeCoproductModuleGluing.map_recovery 𝒰.X f ij.2)

end FLT.Mazur.SchemeFppfFamily
