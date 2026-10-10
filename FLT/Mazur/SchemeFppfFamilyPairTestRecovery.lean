/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfFamilyPairNormalization

/-!
# Recovering original pairs on arbitrary test schemes

An original pair equation restricts to any test scheme with named
coordinates. The result compares the assembled and independent edges.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeFppfFamily
open SheafPullbackCoordinateRecovery SchemeOverlapDiagonalChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] SchemeCoproductModuleGluing.assembled
variable {X T : Scheme.{u}} (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X)
variable (M : ∀ i, (𝒰.X i).Modules) (e : PairIsomorphisms 𝒰 M)

/-- Recover an assembled edge along any test map into an original pair. -/
lemma pairTest_recovery (ij : 𝒰.I₀ × 𝒰.I₀) (q : T ⟶ pair 𝒰 ij)
    (s : T ⟶ Limits.pullback (projection 𝒰) (projection 𝒰))
    (ws : q ≫ pairMap 𝒰 ij = s)
    (d₁ : T ⟶ 𝒰.X ij.1) (d₂ : T ⟶ 𝒰.X ij.2)
    (z₁ z₂ : T ⟶ ∐ 𝒰.X)
    (v₁ : q ≫ Limits.pullback.fst (𝒰.f ij.1) (𝒰.f ij.2) = d₁)
    (v₂ : q ≫ Limits.pullback.snd (𝒰.f ij.1) (𝒰.f ij.2) = d₂)
    (w₁ : d₁ ≫ Limits.Sigma.ι 𝒰.X ij.1 = z₁)
    (w₂ : d₂ ≫ Limits.Sigma.ι 𝒰.X ij.2 = z₂)
    (u₁ : s ≫ Limits.pullback.fst (projection 𝒰) (projection 𝒰) = z₁)
    (u₂ : s ≫ Limits.pullback.snd (projection 𝒰) (projection 𝒰) = z₂) :
    (normalize (Limits.pullback.fst (projection 𝒰) (projection 𝒰))
      (Limits.pullback.snd (projection 𝒰) (projection 𝒰)) s z₁ z₂ u₁ u₂
      (SchemeCoproductModuleGluing.assembled 𝒰.X M) (assembledOverlap 𝒰 M e)).hom ≫
        (recovery d₂ (Limits.Sigma.ι 𝒰.X ij.2) z₂ w₂
          (SchemeCoproductModuleGluing.assembled 𝒰.X M)
          (SchemeCoproductModuleGluing.recovery 𝒰.X M ij.2)).hom =
      (recovery d₁ (Limits.Sigma.ι 𝒰.X ij.1) z₁ w₁
        (SchemeCoproductModuleGluing.assembled 𝒰.X M)
        (SchemeCoproductModuleGluing.recovery 𝒰.X M ij.1)).hom ≫
      (SchemeIndependentPairNormalization.normalize _ _ q d₁ d₂ v₁ v₂
        (M ij.1) (M ij.2) (e ij)).hom := by
  have h₁ : q ≫ (Limits.pullback.fst (𝒰.f ij.1) (𝒰.f ij.2) ≫
      Limits.Sigma.ι 𝒰.X ij.1) = z₁ := by rw [← Category.assoc, v₁, w₁]
  have h₂ : q ≫ (Limits.pullback.snd (𝒰.f ij.1) (𝒰.f ij.2) ≫
      Limits.Sigma.ι 𝒰.X ij.2) = z₂ := by rw [← Category.assoc, v₂, w₂]
  have hh := SchemeIndependentRecoveryNormalization.normalize_recovery
    (Limits.pullback.fst (𝒰.f ij.1) (𝒰.f ij.2))
    (Limits.pullback.snd (𝒰.f ij.1) (𝒰.f ij.2))
    (Limits.Sigma.ι 𝒰.X ij.1) (Limits.Sigma.ι 𝒰.X ij.2) _ _ rfl rfl
    q d₁ d₂ z₁ z₂ v₁ v₂ h₁ h₂ w₁ w₂ (SchemeCoproductModuleGluing.assembled 𝒰.X M)
    (SchemeCoproductModuleGluing.recovery 𝒰.X M ij.1)
    (SchemeCoproductModuleGluing.recovery 𝒰.X M ij.2)
    (normalizedPair 𝒰 M e ij) (e ij) (normalizedPair_recovery 𝒰 M e ij)
  have hn := normalize_comp_of_eq (Limits.pullback.fst (projection 𝒰) (projection 𝒰))
    (Limits.pullback.snd (projection 𝒰) (projection 𝒰)) (pairMap 𝒰 ij) _ _
    (pairMap_fst 𝒰 ij) (pairMap_snd 𝒰 ij) q s ws z₁ z₂ h₁ h₂ u₁ u₂
    (SchemeCoproductModuleGluing.assembled 𝒰.X M) (assembledOverlap 𝒰 M e)
  change SchemeIndependentPairNormalization.normalize _ _ q z₁ z₂ h₁ h₂ _ _
    (normalizedPair 𝒰 M e ij) = _ at hn
  rw [hn] at hh
  exact hh

/-- Recovery also compares a normalized total edge after restriction to a test scheme. -/
lemma pairTest_normalize_recovery {T' : Scheme.{u}}
    (ij : 𝒰.I₀ × 𝒰.I₀) (q : T ⟶ pair 𝒰 ij) (t : T ⟶ T')
    (p : T' ⟶ Limits.pullback (projection 𝒰) (projection 𝒰))
    (c₁ c₂ : T' ⟶ ∐ 𝒰.X)
    (h₁ : p ≫ Limits.pullback.fst (projection 𝒰) (projection 𝒰) = c₁)
    (h₂ : p ≫ Limits.pullback.snd (projection 𝒰) (projection 𝒰) = c₂)
    (ws : t ≫ p = q ≫ pairMap 𝒰 ij)
    (d₁ : T ⟶ 𝒰.X ij.1) (d₂ : T ⟶ 𝒰.X ij.2)
    (v₁ : q ≫ Limits.pullback.fst (𝒰.f ij.1) (𝒰.f ij.2) = d₁)
    (v₂ : q ≫ Limits.pullback.snd (𝒰.f ij.1) (𝒰.f ij.2) = d₂)
    (w₁ : d₁ ≫ Limits.Sigma.ι 𝒰.X ij.1 = t ≫ c₁)
    (w₂ : d₂ ≫ Limits.Sigma.ι 𝒰.X ij.2 = t ≫ c₂) :
    (normalize c₁ c₂ t (t ≫ c₁) (t ≫ c₂) rfl rfl
      (SchemeCoproductModuleGluing.assembled 𝒰.X M)
      (normalize (Limits.pullback.fst (projection 𝒰) (projection 𝒰))
        (Limits.pullback.snd (projection 𝒰) (projection 𝒰)) p c₁ c₂ h₁ h₂
        (SchemeCoproductModuleGluing.assembled 𝒰.X M) (assembledOverlap 𝒰 M e))).hom ≫
      (recovery d₂ (Limits.Sigma.ι 𝒰.X ij.2) (t ≫ c₂) w₂
        (SchemeCoproductModuleGluing.assembled 𝒰.X M)
        (SchemeCoproductModuleGluing.recovery 𝒰.X M ij.2)).hom =
    (recovery d₁ (Limits.Sigma.ι 𝒰.X ij.1) (t ≫ c₁) w₁
      (SchemeCoproductModuleGluing.assembled 𝒰.X M)
      (SchemeCoproductModuleGluing.recovery 𝒰.X M ij.1)).hom ≫
      (SchemeIndependentPairNormalization.normalize _ _ q d₁ d₂ v₁ v₂
        (M ij.1) (M ij.2) (e ij)).hom := by
  have u₁ : (t ≫ p) ≫ Limits.pullback.fst _ _ = t ≫ c₁ := by
    rw [Category.assoc, h₁]
  have u₂ : (t ≫ p) ≫ Limits.pullback.snd _ _ = t ≫ c₂ := by
    rw [Category.assoc, h₂]
  rw [normalize_comp _ _ p c₁ c₂ h₁ h₂ t _ _ rfl rfl u₁ u₂]
  exact pairTest_recovery 𝒰 M e ij q (t ≫ p) ws.symm d₁ d₂ _ _
    v₁ v₂ w₁ w₂ u₁ u₂

end FLT.Mazur.SchemeFppfFamily
