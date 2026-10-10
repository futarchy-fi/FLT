/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Original scalars on a spectrum chart

A chart morphism presented by a map into an original affine chart induces
exactly that ring map on sections, after the canonical spectrum identification.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.AffineChartSourceScalars

/-- The canonical original affine chart has the original scalar coordinates. -/
lemma fromSpec_appLE {X : Scheme.{u}} (V : X.affineOpens)
    (h : ⊤ ≤ V.2.fromSpec ⁻¹ᵁ V.1) :
    V.2.fromSpec.appLE V.1 ⊤ h = (Scheme.ΓSpecIso Γ(X, V.1)).inv := by
  rw [Scheme.Hom.appLE, V.2.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  have he : (eqToHom V.2.fromSpec_preimage_self).op ≫ (homOfLE h).op = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [he, (Spec Γ(X, V.1)).presheaf.map_id, Category.comp_id]

/-- A spectrum chart over an original affine open retains its specified ring map. -/
lemma chart_appLE {X : Scheme.{u}} (V : X.affineOpens) (A : CommRingCat.{u})
    (a : Γ(X, V.1) ⟶ A) (c : Spec A ⟶ X)
    (hc : c = Spec.map a ≫ V.2.fromSpec) (h : ⊤ ≤ c ⁻¹ᵁ V.1) :
    c.appLE V.1 ⊤ h = a ≫ (Scheme.ΓSpecIso A).inv := by
  subst c
  have hV : ⊤ ≤ V.2.fromSpec ⁻¹ᵁ V.1 := by rw [V.2.fromSpec_preimage_self]
  have hA : ⊤ ≤ Spec.map a ⁻¹ᵁ ⊤ := by simp
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map a) V.2.fromSpec V.1 ⊤ ⊤ hV hA,
    fromSpec_appLE]
  change (Scheme.ΓSpecIso Γ(X, V.1)).inv ≫ (Spec.map a).appTop = _
  exact (Scheme.ΓSpecIso_inv_naturality a).symm

end FLT.Mazur.AffineChartSourceScalars
