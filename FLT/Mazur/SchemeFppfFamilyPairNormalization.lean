/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfFamilyOverlapAssembly
public import FLT.Mazur.SchemeIndependentRecoveryNormalization
public import FLT.Mazur.SchemeOverlapTransportComposition

/-!
# Normalized recovery of original family pairs

The assembled overlap on an original pair intertwines the independently
supplied pair isomorphism through its two coordinate recoveries.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeFppfFamily
open SheafPullbackPathComparison SheafPullbackCoordinateRecovery
open SchemeOverlapDiagonalChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] SchemeCoproductModuleGluing.assembled
variable {X : Scheme.{u}} (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X)
variable (M : ∀ i, (𝒰.X i).Modules)

/-- Normalize the assembled overlap to the two original pair coordinates. -/
def normalizedPair (e : PairIsomorphisms 𝒰 M) (ij : 𝒰.I₀ × 𝒰.I₀) :=
  normalize (Limits.pullback.fst (projection 𝒰) (projection 𝒰))
    (Limits.pullback.snd (projection 𝒰) (projection 𝒰)) (pairMap 𝒰 ij)
    (Limits.pullback.fst (𝒰.f ij.1) (𝒰.f ij.2) ≫ Limits.Sigma.ι 𝒰.X ij.1)
    (Limits.pullback.snd (𝒰.f ij.1) (𝒰.f ij.2) ≫ Limits.Sigma.ι 𝒰.X ij.2)
    (pairMap_fst 𝒰 ij) (pairMap_snd 𝒰 ij)
    (SchemeCoproductModuleGluing.assembled 𝒰.X M) (assembledOverlap 𝒰 M e)

/-- The first pair recovery factors through the normalized coordinate recovery. -/
lemma pairLeftRecovery_coordinate (ij : 𝒰.I₀ × 𝒰.I₀) :
    (pairLeftRecovery 𝒰 M ij).hom =
      (comparison (pairMap 𝒰 ij) (Limits.pullback.fst _ _) _
        (pairMap_fst 𝒰 ij)).hom.app (SchemeCoproductModuleGluing.assembled 𝒰.X M) ≫
      (recovery (Limits.pullback.fst (𝒰.f ij.1) (𝒰.f ij.2))
        (Limits.Sigma.ι 𝒰.X ij.1) _ rfl (SchemeCoproductModuleGluing.assembled 𝒰.X M)
        (SchemeCoproductModuleGluing.recovery 𝒰.X M ij.1)).hom := by
  simp only [pairLeftRecovery, recovery, comparison, pullbackCongr, eqToIso_refl,
    Iso.trans_refl, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    NatTrans.comp_app, Functor.mapIso_hom, Category.assoc]

/-- The second pair recovery factors through the normalized coordinate recovery. -/
lemma pairRightRecovery_coordinate (ij : 𝒰.I₀ × 𝒰.I₀) :
    (pairRightRecovery 𝒰 M ij).hom =
      (comparison (pairMap 𝒰 ij) (Limits.pullback.snd _ _) _
        (pairMap_snd 𝒰 ij)).hom.app (SchemeCoproductModuleGluing.assembled 𝒰.X M) ≫
      (recovery (Limits.pullback.snd (𝒰.f ij.1) (𝒰.f ij.2))
        (Limits.Sigma.ι 𝒰.X ij.2) _ rfl (SchemeCoproductModuleGluing.assembled 𝒰.X M)
        (SchemeCoproductModuleGluing.recovery 𝒰.X M ij.2)).hom := by
  simp only [pairRightRecovery, recovery, comparison, pullbackCongr, eqToIso_refl,
    Iso.trans_refl, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    NatTrans.comp_app, Functor.mapIso_hom, Category.assoc]

/-- The normalized assembled pair recovers the original independent pair isomorphism. -/
lemma normalizedPair_recovery (e : PairIsomorphisms 𝒰 M) (ij : 𝒰.I₀ × 𝒰.I₀) :
    (normalizedPair 𝒰 M e ij).hom ≫
      (recovery (Limits.pullback.snd (𝒰.f ij.1) (𝒰.f ij.2))
        (Limits.Sigma.ι 𝒰.X ij.2) _ rfl (SchemeCoproductModuleGluing.assembled 𝒰.X M)
        (SchemeCoproductModuleGluing.recovery 𝒰.X M ij.2)).hom =
    (recovery (Limits.pullback.fst (𝒰.f ij.1) (𝒰.f ij.2))
      (Limits.Sigma.ι 𝒰.X ij.1) _ rfl (SchemeCoproductModuleGluing.assembled 𝒰.X M)
      (SchemeCoproductModuleGluing.recovery 𝒰.X M ij.1)).hom ≫ (e ij).hom := by
  apply (cancel_epi ((comparison (pairMap 𝒰 ij) (Limits.pullback.fst _ _) _
    (pairMap_fst 𝒰 ij)).hom.app (SchemeCoproductModuleGluing.assembled 𝒰.X M))).mp
  dsimp only [normalizedPair, SchemeOverlapDiagonalChart.normalize, Iso.trans_hom,
    Iso.symm_hom, Iso.app_inv, Iso.app_hom, Functor.mapIso_hom]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← pairRightRecovery_coordinate, ← Category.assoc, ← pairLeftRecovery_coordinate]
  exact assembledOverlap_recovery 𝒰 M e ij

end FLT.Mazur.SchemeFppfFamily
