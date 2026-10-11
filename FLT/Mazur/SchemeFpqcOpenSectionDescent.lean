/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOpenSectionDescent
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Faithfully flat descent on every original open

Quasi-compact faithfully flat covers descend regular functions on every target
open. No finite-presentation assumption is needed; this applies to constructed
affine algebra descent projections. All section maps retain their original domains.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.SchemeEffectiveEpiSections.Fpqc
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y P : Scheme.{u}} {g : Y ⟶ X} {a b : P ⟶ Y}
  (H : IsPullback a b g g) (W : X.Opens)

variable [Flat g] [Surjective g] [QuasiCompact g]

/-- The faithfully flat cover detects sections on every original target open. -/
theorem app_injective : Function.Injective (g.app W) := by
  let _ : Surjective (g ∣_ W) :=
    IsZariskiLocalAtTarget.restrict (P := @Surjective) inferInstance W
  intro s t h
  apply W.topIso.symm.commRingCatIsoToRingEquiv.injective
  apply appTop_injective (g ∣_ W)
  rw [← g.resLE_eq_morphismRestrict (U := W)]
  change (g.resLE W (g ⁻¹ᵁ W) le_rfl).appTop (W.topIso.inv s) =
    (g.resLE W (g ⁻¹ᵁ W) le_rfl).appTop (W.topIso.inv t)
  simp only [resLE_appTop_coordinates, Scheme.Hom.appLE_eq_app,
    ConcreteCategory.comp_apply, Iso.inv_hom_id_apply, h]

/-- A compatible original source section descends on its actual target open. -/
theorem app_existsUnique (s : Γ(Y, g ⁻¹ᵁ W))
    (hs : a.app (g ⁻¹ᵁ W) s =
      b.appLE (g ⁻¹ᵁ W) (a ⁻¹ᵁ (g ⁻¹ᵁ W)) (kernelPair_preimage_open H W).le s) :
    ∃! t : Γ(X, W), g.app W t = s := by
  let _ : Surjective (g ∣_ W) :=
    IsZariskiLocalAtTarget.restrict (P := @Surjective) inferInstance W
  have hh : (openKernelFst (a := a) (g := g) W).appTop ((g ⁻¹ᵁ W).topIso.inv s) =
      (openKernelSnd H W).appTop ((g ⁻¹ᵁ W).topIso.inv s) := by
    simp only [openKernelFst, openKernelSnd, resLE_appTop_coordinates,
      Scheme.Hom.appLE_eq_app, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply, hs]
  obtain ⟨t, ht, _⟩ := sections_existsUnique (openKernel_isPullback H W)
    ((g ⁻¹ᵁ W).topIso.inv s) hh
  have ht' : g.app W (W.topIso.hom t) = s := by
    apply (g ⁻¹ᵁ W).topIso.symm.commRingCatIsoToRingEquiv.injective
    change (g ⁻¹ᵁ W).topIso.inv (g.app W (W.topIso.hom t)) =
      (g ⁻¹ᵁ W).topIso.inv s
    rw [← g.resLE_eq_morphismRestrict (U := W)] at ht
    simpa only [resLE_appTop_coordinates, Scheme.Hom.appLE_eq_app,
      ConcreteCategory.comp_apply] using ht
  exact ⟨W.topIso.hom t, ht', fun z hz ↦ app_injective W (hz.trans ht'.symm)⟩

end FLT.Mazur.SchemeEffectiveEpiSections.Fpqc
