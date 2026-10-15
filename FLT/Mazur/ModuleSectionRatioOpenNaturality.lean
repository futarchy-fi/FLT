/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ModuleSectionRatioAlongMorphism

/-!
# Local section ratios under arbitrary scheme morphisms

The actual structure-sheaf map carries a normalized section ratio to the
ratio of the pulled-back sections, including on infinitesimal closed stages.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Scheme.Modules
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
  (U : Y.Opens) (V : X.Opens) (hV : V ≤ f ⁻¹ᵁ U)

/-- The adjunction unit on an open retains the restriction of the global pullback. -/
theorem pullGlobal_fromOpen_restrict (x : Γ(M, ⊤)) :
    ((pullback f).obj M).presheaf.map (homOfLE hV).op
      (((pullbackPushforwardAdjunction f).unit.app M).app U
        (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op x)) =
      ((pullback f).obj M).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (pullGlobal f M x) := by
  have hn := ConcreteCategory.congr_hom
    (((pullbackPushforwardAdjunction f).unit.app M).mapPresheaf.naturality
      (homOfLE (show U ≤ ⊤ from le_top)).op) x
  change ((pullbackPushforwardAdjunction f).unit.app M).app U
    (M.presheaf.map (homOfLE le_top).op x) =
      ((pullback f).obj M).presheaf.map (homOfLE le_top).op (pullGlobal f M x) at hn
  rw [hn, ← Functor.map_comp_apply]
  rfl

/-- Local normalized coordinates commute with the original scheme pullback. -/
theorem sectionRatioOn_pullback (s t : Γ(M, ⊤))
    (hs : U ≤ sectionGeneratorOpen M s)
    (hsV : V ≤ sectionGeneratorOpen ((pullback f).obj M) (pullGlobal f M s)) :
    f.appLE U V hV (sectionRatioOn M s U hs t) =
      sectionRatioOn ((pullback f).obj M) (pullGlobal f M s) V hsV
        (pullGlobal f M t) := by
  symm
  apply (sectionRatioOn_eq_iff _ _ _ _ _ _).mpr
  have he := congrArg (fun z ↦ ((pullback f).obj M).presheaf.map (homOfLE hV).op
    (((pullbackPushforwardAdjunction f).unit.app M).app U z))
    (sectionRatioOn_smul M s U hs t)
  erw [Hom.app_smul, ((pullback f).obj M).val.map_smul] at he
  change f.appLE U V hV (sectionRatioOn M s U hs t) •
    ((pullback f).obj M).presheaf.map (homOfLE hV).op
      (((pullbackPushforwardAdjunction f).unit.app M).app U
        (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s)) = _ at he
  simpa only [pullGlobal_fromOpen_restrict] using he

end FLT.Mazur.FCurve
