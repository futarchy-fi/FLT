/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionRatioOpen

/-!
# Local ratios evaluated in a pulled-back frame

When a morphism lands in a generator open and the denominator has coefficient
one in an actual pulled-back frame, the local ratio evaluates to the numerator's
coefficient. This applies to closed markings as well as open charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Scheme.Modules
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
  (U : Y.Opens) (hU : ⊤ ≤ f ⁻¹ᵁ U)

/-- Restricting an adjunction-unit section back to the whole source is global pullback. -/
theorem pullGlobal_fromOpen (x : Γ(M, ⊤)) :
    ((pullback f).obj M).presheaf.map (homOfLE hU).op
      (((pullbackPushforwardAdjunction f).unit.app M).app U
        (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op x)) =
      pullGlobal f M x := by
  have hn := ConcreteCategory.congr_hom
    (((pullbackPushforwardAdjunction f).unit.app M).mapPresheaf.naturality
      (homOfLE (show U ≤ ⊤ from le_top)).op) x
  change ((pullbackPushforwardAdjunction f).unit.app M).app U
    (M.presheaf.map (homOfLE le_top).op x) =
      ((pullback f).obj M).presheaf.map (homOfLE le_top).op (pullGlobal f M x) at hn
  rw [hn, ← Functor.map_comp_apply]
  exact Functor.map_id_apply _ _ _

/-- A local ratio evaluates to the numerator coefficient when the pulled denominator is one. -/
theorem sectionRatioOn_frame (s t : Γ(M, ⊤))
    (hs : U ≤ sectionGeneratorOpen M s)
    (e : (pullback f).obj M ≅ structureModule X)
    (he : e.hom.app ⊤ (pullGlobal f M s) = (1 : Γ(X, ⊤))) :
    f.appLE U ⊤ hU (sectionRatioOn M s U hs t) =
      e.hom.app ⊤ (pullGlobal f M t) := by
  have h := congrArg (fun z ↦ ((pullback f).obj M).presheaf.map (homOfLE hU).op
    (((pullbackPushforwardAdjunction f).unit.app M).app U z))
    (sectionRatioOn_smul M s U hs t)
  erw [Hom.app_smul, ((pullback f).obj M).val.map_smul] at h
  change f.appLE U ⊤ hU (sectionRatioOn M s U hs t) •
    ((pullback f).obj M).presheaf.map (homOfLE hU).op
      (((pullbackPushforwardAdjunction f).unit.app M).app U
        (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s)) = _ at h
  rw [pullGlobal_fromOpen, pullGlobal_fromOpen] at h
  have hc := congrArg (e.hom.app ⊤) h
  simpa only [Hom.app_smul, he, smul_eq_mul, mul_one] using hc

/-- Evaluating through an open factor uses the original morphism's local section map. -/
theorem openFactor_appTop (g : X ⟶ U.toScheme) (hg : g ≫ U.ι = f)
    (a : Γ(Y, U)) : g.appTop (U.topIso.inv a) = f.appLE U ⊤ hU a := by
  subst f
  have hi : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    simp only [Scheme.Hom.appLE, Scheme.Opens.ι_app_self, Scheme.Opens.topIso_inv]
    change Y.presheaf.map _ ≫ Y.presheaf.map _ = Y.presheaf.map _
    rw [← Functor.map_comp]
    rfl
  have h := Scheme.Hom.appLE_comp_appLE g U.ι U ⊤ ⊤ U.ι_preimage_self.ge le_top
  rw [hi] at h
  have ht : g.appLE ⊤ ⊤ le_top = g.appTop := by
    exact g.appLE_eq_app
  rw [ht] at h
  exact ConcreteCategory.congr_hom h a

end FLT.Mazur.FCurve
