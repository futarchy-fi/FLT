/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Section transport through an affine open image

Factor an affine open immersion through its image and identify the induced
map on sections, including the top-open and Gamma-Spec transports.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.AffineImageSectionTransport
private lemma appLE_eq {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (h : f = g)
    (U : Z.Opens) (V : Y.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (j : Spec (.of R) ⟶ X) [IsOpenImmersion j]

/-- The natural factorization through the image of the whole affine source. -/
def factor : Spec (.of R) ⟶ (j ''ᵁ ⊤).toScheme :=
  (Spec (.of R)).topIso.inv ≫ (j.isoImage ⊤).hom

@[reassoc (attr := simp)]
lemma factor_ι : factor j ≫ (j ''ᵁ ⊤).ι = j := by simp [factor]

/-- Pulling sections through the image factor is the open-immersion section isomorphism. -/
lemma factor_appTop : (j ''ᵁ ⊤).topIso.inv ≫ (factor j).appTop = (j.appIso ⊤).hom := by
  have he := Scheme.Hom.appLE_comp_appLE (factor j) (j ''ᵁ ⊤).ι
    (j ''ᵁ ⊤) ⊤ ⊤ (by rw [Scheme.Opens.ι_preimage_self]) (by simp)
  have hu : (j ''ᵁ ⊤).ι.appLE (j ''ᵁ ⊤) ⊤ (by rw [Scheme.Opens.ι_preimage_self]) =
      (j ''ᵁ ⊤).topIso.inv := by
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    congr 1
  rw [hu] at he
  have he' := he.trans (appLE_eq (factor_ι j) _ _ _
    (show ⊤ ≤ j ⁻¹ᵁ (j ''ᵁ ⊤) by rw [j.preimage_image_eq]))
  simpa [Scheme.Hom.appIso_hom', Scheme.Hom.appLE, Scheme.Hom.appTop] using he'

/-- Spec of the transported ring map is the corresponding affine-image factorization. -/
lemma spec_transport {Q : Type u} [CommRing Q] (r : Q →+* Γ(X, j ''ᵁ ⊤)) :
    Spec.map (CommRingCat.ofHom ((Scheme.ΓSpecIso (.of R)).hom.hom.comp
      ((j.appIso ⊤).hom.hom.comp r))) =
    factor j ≫ (j ''ᵁ ⊤).toScheme.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom ((j ''ᵁ ⊤).topIso.inv.hom.comp r)) := by
  rw [← Category.assoc, Scheme.toSpecΓ_naturality]
  rw [Category.assoc, ← Spec.map_comp, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext z
  change _ = (Scheme.ΓSpecIso (.of R)).hom
    ((factor j).appTop ((j ''ᵁ ⊤).topIso.inv (r z)))
  apply congrArg (Scheme.ΓSpecIso (.of R)).hom
  exact (congrArg (fun f : Γ(X, j ''ᵁ ⊤) ⟶ Γ(Spec (.of R), ⊤) ↦ f (r z))
    (factor_appTop j)).symm

end FLT.Mazur.AffineImageSectionTransport
