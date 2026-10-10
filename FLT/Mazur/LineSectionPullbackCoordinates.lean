/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleGlobalUnitGenerator

/-!
# Regular section coordinates under actual sheaf pullback

A sheaf frame pulls back through the structure-module comparison. Its scalar
is the actual scheme pullback of the original scalar, so monicity on a fiber
implies regularity of that scalar without any chosen section comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
namespace FLT.Mazur.LineSectionPullbackCoordinates
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} {L : Y.Modules}

/-- A genuine line frame pulled through the canonical structure-module comparison. -/
def frame (f : X ⟶ Y) (e : L ≅ structureModule Y) :
    (pullback f).obj L ≅ structureModule X :=
  (pullback f).mapIso e ≪≫ modulePullbackUnitIso f

/-- The scalar of the pulled section is the pullback of its original scalar. -/
lemma frame_section (f : X ⟶ Y) (e : L ≅ structureModule Y) (s : Γ(L, ⊤)) :
    (frame f e).hom.app ⊤ (pullGlobal f L s) = f.appTop (e.hom.app ⊤ s) := by
  change (modulePullbackUnitIso f).hom.app ⊤
    (((pullback f).map e.hom).app ⊤ (pullGlobal f L s)) = _
  rw [pullGlobal_naturality]
  exact modulePullbackUnitIso_unit f ⊤ _

/-- Monicity of a section forces its scalar in any actual frame to be regular. -/
theorem regular_coordinate (e : L ≅ structureModule Y) (s : Γ(L, ⊤))
    [Mono (globalSectionHom L s)] : IsRegular (show Γ(Y, ⊤) from e.hom.app ⊤ s) := by
  have : Mono (globalSectionHom L s).val :=
    inferInstanceAs (Mono ((SheafOfModules.forget _).map (globalSectionHom L s)))
  have hi : Function.Injective ((globalSectionHom L s).val.app (op ⊤)) :=
    PresheafOfModules.injective_of_mono _ _
  rw [← isRightRegular_iff_isRegular]
  intro a b hab
  apply hi
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).injective
  change e.hom.app ⊤ (a • L.presheaf.map (𝟙 (op ⊤)) s) =
    e.hom.app ⊤ (b • L.presheaf.map (𝟙 (op ⊤)) s)
  simpa only [L.presheaf.map_id, ConcreteCategory.id_apply, Hom.app_smul, smul_eq_mul]
    using hab

/-- Fiber monicity detects the original scalar after its actual scheme pullback. -/
theorem regular_pulled_coordinate (f : X ⟶ Y) (e : L ≅ structureModule Y)
    (s : Γ(L, ⊤)) [Mono (globalSectionHom _ (pullGlobal f L s))] :
    IsRegular (f.appTop (e.hom.app ⊤ s)) := by
  rw [← frame_section]
  exact regular_coordinate (frame f e) (pullGlobal f L s)

end FLT.Mazur.LineSectionPullbackCoordinates
