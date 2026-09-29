/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.LocalProperties

/-!
# Detecting module-sheaf isomorphisms on open covers

Scheme restriction evaluates sections on the image of an open. Slice restriction
instead evaluates directly on a subopen. The image-preimage identity transports
invertibility between these restrictions. Sheaf local isomorphism detection then
applies, and the module forgetful functor reflects the resulting isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u v

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve.ModuleSheafOpenIsoDetection

variable {X : Scheme.{u}} {M N : X.Modules}

/-- Scheme restriction detects invertibility of section maps on every subopen. -/
lemma isIso_app_of_restrict (f : M ⟶ N) (U V : X.Opens) (hVU : V ≤ U)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)] : IsIso (f.app V) := by
  have h : IsIso (((Scheme.Modules.restrictFunctor U.ι).map f).app (U.ι ⁻¹ᵁ V)) :=
    inferInstance
  change IsIso (f.app (U.ι ''ᵁ (U.ι ⁻¹ᵁ V))) at h
  have he : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hVU]
  exact he ▸ h

/-- An invertible scheme restriction gives an invertible restriction to the slice site. -/
lemma isIso_overPullback_of_restrict (f : M ⟶ N) (U : X.Opens)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)] :
    IsIso (((Opens.grothendieckTopology X).overPullback Ab U).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map f)) := by
  rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
  intro V
  change IsIso (f.app V.unop.left)
  exact isIso_app_of_restrict f U V.unop.left (leOfHom V.unop.hom)

/-- Conversely, invertibility on the slice implies invertibility of scheme restriction. -/
lemma isIso_restrict_of_overPullback (f : M ⟶ N) (U : X.Opens)
    [IsIso (((Opens.grothendieckTopology X).overPullback Ab U).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map f))] :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map f) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro V
  have hVU : U.ι ''ᵁ V ≤ U := by
    simpa only [Scheme.Opens.opensRange_ι] using U.ι.image_le_opensRange V
  let W : Over U := Over.mk (homOfLE hVU)
  have h := (NatTrans.isIso_iff_isIso_app
    (((Opens.grothendieckTopology X).overPullback Ab U).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map f)).hom).mp
        inferInstance (op W)
  exact h

/-- The two concrete restrictions give exactly the same isomorphism test. -/
lemma isIso_restrict_iff_overPullback (f : M ⟶ N) (U : X.Opens) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map f) ↔
      IsIso (((Opens.grothendieckTopology X).overPullback Ab U).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map f)) :=
  ⟨fun _ ↦ isIso_overPullback_of_restrict f U, fun _ ↦ isIso_restrict_of_overPullback f U⟩

/-- A pointwise covering family of opens covers the terminal object of the site. -/
lemma coversTop_of_cover {ι : Type v} (U : ι → X.Opens)
    (hU : ∀ x : X, ∃ i, x ∈ U i) : (Opens.grothendieckTopology X).CoversTop U := by
  intro V x hx
  obtain ⟨i, hi⟩ := hU x
  exact ⟨V ⊓ U i, homOfLE inf_le_left,
    ⟨i, ⟨homOfLE inf_le_right⟩⟩, ⟨hx, hi⟩⟩

/-- Module morphisms are invertible when their restrictions to a covering family are. -/
theorem isIso_of_openCover (f : M ⟶ N) {ι : Type v} (U : ι → X.Opens)
    (hU : ∀ x : X, ∃ i, x ∈ U i)
    (hf : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (U i).ι).map f)) : IsIso f := by
  have h : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map f) :=
    Sheaf.isIso_of_coversTop (coversTop_of_cover U hU) (fun i ↦ by
      let hfi := hf i
      exact isIso_overPullback_of_restrict f (U i))
  have hpresheaf : IsIso ((Scheme.Modules.toPresheaf X).map f) :=
    inferInstanceAs (IsIso ((sheafToPresheaf (Opens.grothendieckTopology X) Ab).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map f)))
  exact isIso_of_reflects_iso f (Scheme.Modules.toPresheaf X)

/-- The open-cover criterion is an equivalence, with no chosen local inverses. -/
theorem isIso_iff_openCover (f : M ⟶ N) {ι : Type v} (U : ι → X.Opens)
    (hU : ∀ x : X, ∃ i, x ∈ U i) :
    IsIso f ↔ ∀ i, IsIso ((Scheme.Modules.restrictFunctor (U i).ι).map f) :=
  ⟨fun _ _ ↦ inferInstance, isIso_of_openCover f U hU⟩

/-- The same criterion with the cover expressed as a supremum of opens. -/
theorem isIso_of_iSup_eq_top (f : M ⟶ N) {ι : Type v} (U : ι → X.Opens)
    (hU : iSup U = ⊤)
    (hf : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (U i).ι).map f)) : IsIso f := by
  apply isIso_of_openCover f U _ hf
  intro x
  exact Opens.mem_iSup.mp (show x ∈ iSup U by rw [hU]; trivial)

/-- Construct the global isomorphism from the local invertibility test. -/
def isoOfOpenCover (f : M ⟶ N) {ι : Type v} (U : ι → X.Opens)
    (hU : ∀ x : X, ∃ i, x ∈ U i)
    (hf : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (U i).ι).map f)) : M ≅ N := by
  letI hglobal := isIso_of_openCover f U hU hf
  exact asIso f

@[simp]
lemma isoOfOpenCover_hom (f : M ⟶ N) {ι : Type v} (U : ι → X.Opens)
    (hU : ∀ x : X, ∃ i, x ∈ U i)
    (hf : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (U i).ι).map f)) :
    (isoOfOpenCover f U hU hf).hom = f := rfl

end FLT.Mazur.FCurve.ModuleSheafOpenIsoDetection
