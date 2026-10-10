/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Pullback of general graded Proj chart sections

The Proj chart isomorphism and the Gamma-Spec adjunction identify actual
structure-sheaf pullbacks with the ring homomorphism defining a local map.
-/

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.GradedProjChartSections
variable {A : Type u} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] (s : A) {d : ℕ} (hs : s ∈ 𝒜 d) (hd : 0 < d)
/-- The inverse chart isomorphism recovers the coordinate ring section. -/
lemma chartSection_iso_inv :
    Proj.awayToSection 𝒜 s ≫
      (Proj.basicOpen 𝒜 s).topIso.inv ≫ (Proj.basicOpenIsoSpec 𝒜 s hs hd).inv.appTop =
        (Scheme.ΓSpecIso (.of (Away 𝒜 s))).inv := by
  have h := Proj.basicOpenToSpec_app_top 𝒜 s
  change (Proj.basicOpenIsoSpec 𝒜 s hs hd).hom.appTop = _ at h
  rw [← Iso.inv_comp_eq] at h
  rw [← Category.assoc, ← h]
  simp [← Scheme.Hom.comp_appTop]

/-- The chart immersion has its entire source over its own chart. -/
lemma chartMap_chart_preimage_top :
    (Proj.awayι 𝒜 s hs hd) ⁻¹ᵁ Proj.basicOpen 𝒜 s = ⊤ := by
  rw [Proj.awayι, Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self,
    Scheme.Hom.preimage_top]

/-- Pulling a chart section back to its spectrum recovers the original ring element. -/
lemma chartSection_chartMap (hi : (⊤ : (Spec (.of (Away 𝒜 s))).Opens) ≤
    (Proj.awayι 𝒜 s hs hd) ⁻¹ᵁ Proj.basicOpen 𝒜 s) :
    Proj.awayToSection 𝒜 s ≫
      (Proj.awayι 𝒜 s hs hd).appLE (Proj.basicOpen 𝒜 s) ⊤ hi =
        (Scheme.ΓSpecIso (.of (Away 𝒜 s))).inv := by
  have he := Scheme.Hom.appLE_comp_appLE (Proj.basicOpenIsoSpec 𝒜 s hs hd).inv
    (Proj.basicOpen 𝒜 s).ι
    (Proj.basicOpen 𝒜 s) ⊤ ⊤ (by simp) (by simp)
  change _ = (Proj.awayι 𝒜 s hs hd).appLE _ _ _ at he
  rw [← he]
  change Proj.awayToSection 𝒜 s ≫
    (Proj.basicOpen 𝒜 s).topIso.inv ≫ (Proj.basicOpenIsoSpec 𝒜 s hs hd).inv.appTop = _
  exact chartSection_iso_inv 𝒜 s hs hd

/-- A local factorization through a chart computes the actual structure-sheaf pullback. -/
lemma chartSection_evaluation {X : Scheme.{u}} (U : X.Opens)
    (φ : Away 𝒜 s →+* Γ(X, U))
    (f : X ⟶ Proj 𝒜) (hi : U ≤ f ⁻¹ᵁ Proj.basicOpen 𝒜 s)
    (hf : U.ι ≫ f = U.toScheme.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (U.topIso.inv.hom.comp φ)) ≫ Proj.awayι 𝒜 s hs hd) :
    Proj.awayToSection 𝒜 s ≫ f.appLE (Proj.basicOpen 𝒜 s) U hi =
      CommRingCat.ofHom φ := by
  apply (cancel_mono U.topIso.inv).mp
  have hleft := Scheme.Hom.appLE_comp_appLE U.ι f (Proj.basicOpen 𝒜 s) U ⊤ hi (by simp)
  have hright := Scheme.Hom.appLE_comp_appLE
    (U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (U.topIso.inv.hom.comp φ)))
    (Proj.awayι 𝒜 s hs hd) (Proj.basicOpen 𝒜 s) ⊤ ⊤
    (by rw [chartMap_chart_preimage_top 𝒜 s hs hd]) (by simp)
  have hu : U.ι.appLE U ⊤ (by simp) = U.topIso.inv := by
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    congr 1
  rw [hu] at hleft
  rw [Category.assoc, hleft]
  simp only [hf, ← Category.assoc]
  rw [← hright, ← Category.assoc, chartSection_chartMap]
  simp [Scheme.Hom.appLE]
  rfl
/-- The pointwise form of chart evaluation, with the sheaf calculation sealed. -/
lemma chartSection_evaluation_apply {X : Scheme.{u}} (U : X.Opens)
    (φ : Away 𝒜 s →+* Γ(X, U))
    (f : X ⟶ Proj 𝒜) (hi : U ≤ f ⁻¹ᵁ Proj.basicOpen 𝒜 s)
    (hf : U.ι ≫ f = U.toScheme.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (U.topIso.inv.hom.comp φ)) ≫ Proj.awayι 𝒜 s hs hd)
    (z : Away 𝒜 s) :
    f.appLE (Proj.basicOpen 𝒜 s) U hi (Proj.awayToSection 𝒜 s z) =
      φ z :=
  ConcreteCategory.congr_hom (chartSection_evaluation 𝒜 s hs hd U φ f hi hf) z

end FLT.Mazur.GradedProjChartSections
