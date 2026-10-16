/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModulePullbackStageGlobalSections
public import FLT.Mazur.ModuleSectionMap

/-!
# Retaining a marking frame through a commuting stage square

Transport of a section followed by evaluation in the transported frame is
the original scalar evaluation pulled back along the actual base map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y S T : Scheme.{u}} (f : X ⟶ Y) (p : T ⟶ X) (s : S ⟶ Y) (b : T ⟶ S)
variable (h : p ≫ f = b ≫ s) {L : Y.Modules} {M : X.Modules}
variable (e : (pullback f).obj L ≅ M) (v : (pullback s).obj L ≅ structureModule S)

/-- The retained frame on the same marking after the specified line comparison. -/
irreducible_def comparedMarkingFrame : (pullback p).obj M ≅ structureModule T :=
  (pullback p).mapIso e.symm ≪≫ pullbackStageIso (b ≫ s) f p h L ≪≫
    ((pullbackComp b s).app L).symm ≪≫ (pullback b).mapIso v ≪≫ modulePullbackUnitIso b

/-- In this frame, the original section coefficient changes only by the original base map. -/
theorem comparedMarkingFrame_section (t : Γ(L, ⊤)) :
    (comparedMarkingFrame f p s b h e v).hom.app ⊤
        (pullGlobal p M (e.hom.app ⊤ (pullGlobal f L t))) =
      b.appTop (v.hom.app ⊤ (pullGlobal s L t)) := by
  rw [comparedMarkingFrame_def]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Hom.comp_app, ConcreteCategory.comp_apply]
  rw [pullGlobal_naturality, sectionIso_inv_hom, pullbackStageIso_globalSection]
  change (modulePullbackUnitIso b).hom.app ⊤
    (((pullback b).map v.hom).app ⊤
      (((pullbackComp b s).inv.app L).app ⊤ (pullGlobal (b ≫ s) L t))) = _
  rw [pullGlobal_comp, pullGlobal_naturality]
  exact modulePullbackUnitIso_unit b ⊤ _

end FLT.Mazur.FCurve
