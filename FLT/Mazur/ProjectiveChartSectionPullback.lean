/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveCoherentCharts

/-!
# Pullback of projective chart sections

The Proj chart isomorphism and the Gamma-Spec adjunction identify actual
structure-sheaf pullbacks with the ring homomorphism defining a local map.
-/

open CategoryTheory AlgebraicGeometry MvPolynomial
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type u) [CommRing R] (ι : Type u)
/-- The inverse chart isomorphism recovers the coordinate ring section. -/
lemma chartSection_iso_inv (i : ι) :
    Proj.awayToSection (grading R ι) (MvPolynomial.X i) ≫
      (chart R ι i).topIso.inv ≫ (chartIso R ι i).inv.appTop =
        (Scheme.ΓSpecIso (.of (chartRing R ι i))).inv := by
  have h := Proj.basicOpenToSpec_app_top (grading R ι) (MvPolynomial.X i)
  change (chartIso R ι i).hom.appTop = _ at h
  rw [← Iso.inv_comp_eq] at h
  dsimp only [chart]
  rw [← Category.assoc, ← h]
  simp [← Scheme.Hom.comp_appTop]

/-- The chart immersion has its entire source over its own chart. -/
lemma chartMap_chart_preimage_top (i : ι) :
    (chartMap R ι i) ⁻¹ᵁ chart R ι i = ⊤ := by
  rw [chartMap, Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self,
    Scheme.Hom.preimage_top]

/-- Pulling a chart section back to its spectrum recovers the original ring element. -/
lemma chartSection_chartMap (i : ι) (hi : (⊤ : (Spec (.of (chartRing R ι i))).Opens) ≤
    (chartMap R ι i) ⁻¹ᵁ chart R ι i) :
    Proj.awayToSection (grading R ι) (MvPolynomial.X i) ≫
      (chartMap R ι i).appLE (chart R ι i) ⊤ hi =
        (Scheme.ΓSpecIso (.of (chartRing R ι i))).inv := by
  have he := Scheme.Hom.appLE_comp_appLE (chartIso R ι i).inv (chart R ι i).ι
    (chart R ι i) ⊤ ⊤ (by simp) (by simp)
  change _ = (chartMap R ι i).appLE _ _ _ at he
  rw [← he]
  change Proj.awayToSection (grading R ι) (MvPolynomial.X i) ≫
    (chart R ι i).topIso.inv ≫ (chartIso R ι i).inv.appTop = _
  exact chartSection_iso_inv R ι i

/-- A local factorization through a chart computes the actual structure-sheaf pullback. -/
lemma chartSection_evaluation {X : Scheme.{u}} (i : ι) (U : X.Opens)
    (φ : chartRing R ι i →+* Γ(X, U))
    (f : X ⟶ space R ι) (hi : U ≤ f ⁻¹ᵁ chart R ι i)
    (hf : U.ι ≫ f = U.toScheme.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (U.topIso.inv.hom.comp φ)) ≫ chartMap R ι i) :
    Proj.awayToSection (grading R ι) (MvPolynomial.X i) ≫ f.appLE (chart R ι i) U hi =
      CommRingCat.ofHom φ := by
  apply (cancel_mono U.topIso.inv).mp
  have hleft := Scheme.Hom.appLE_comp_appLE U.ι f (chart R ι i) U ⊤ hi (by simp)
  have hright := Scheme.Hom.appLE_comp_appLE
    (U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (U.topIso.inv.hom.comp φ)))
    (chartMap R ι i) (chart R ι i) ⊤ ⊤
    (by rw [chartMap_chart_preimage_top]) (by simp)
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
lemma chartSection_evaluation_apply {X : Scheme.{u}} (i : ι) (U : X.Opens)
    (φ : chartRing R ι i →+* Γ(X, U))
    (f : X ⟶ space R ι) (hi : U ≤ f ⁻¹ᵁ chart R ι i)
    (hf : U.ι ≫ f = U.toScheme.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (U.topIso.inv.hom.comp φ)) ≫ chartMap R ι i)
    (z : chartRing R ι i) :
    f.appLE (chart R ι i) U hi (Proj.awayToSection (grading R ι) (MvPolynomial.X i) z) =
      φ z :=
  ConcreteCategory.congr_hom (chartSection_evaluation R ι i U φ f hi hf) z

end FLT.Mazur.ProjectiveSpace
