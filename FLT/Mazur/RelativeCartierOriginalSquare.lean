/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeCartierIdealPullback

/-!
# Relative Cartier pullback on an independently specified cartesian square

The canonical fiber-product identification carries both the full ideal and
its actual module comparison to the original test total space.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits
open Scheme.Modules
universe u
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {P X T S : Scheme.{u}} {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) (I : X.IdealSheafData) (hI : RelativeEffectiveCartier f I)

include h hI

/-- Arbitrary relative Cartier pullback retains the original square and its full ideal. -/
theorem relativeCartier_originalSquare : RelativeEffectiveCartier q (I.comap p) := by
  have hr := (relativeCartierBaseChange f g I hI).comap_of_isOpenImmersion h.isoPullback.hom
  simpa only [← Scheme.IdealSheafData.comap_comp, h.isoPullback_hom_fst,
    h.isoPullback_hom_snd] using hr

/-- The actual ideal module comparison is invertible on the original cartesian total space. -/
theorem relativeCartierIdealPullback_originalSquare : IsIso (idealModulePullbackHom I p) := by
  let _ := relativeCartierIdealPullback f g I hI
  have hw : h.isoPullback.hom ≫ pullback.fst f g = p ≫ 𝟙 X := by
    rw [h.isoPullback_hom_fst, Category.comp_id]
  have he := idealModulePullbackHom_restrict I (pullback.fst f g) p
    h.isoPullback.hom (𝟙 X) hw
  have hi := (Iff.of_eq (congrArg IsIso he)).mp inferInstance
  have hm : IsIso (idealModulePullbackHom (I.comap (𝟙 X)) p) := by
    simpa only [isIso_comp_left_iff] using hi
  exact (congrArg (fun J ↦ IsIso (idealModulePullbackHom J p)) I.comap_id).mp hm

end FLT.Mazur.FCurve
