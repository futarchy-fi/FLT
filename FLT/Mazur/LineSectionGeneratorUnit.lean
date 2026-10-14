/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionRatioOpen
public import FLT.Mazur.AmpleLineBundle

/-!
# A generating section is a unit in every line frame

The actual inverse section map gives the inverse of its scalar coordinate.
The ambient scheme need not be affine or reduced.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules Opposite
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {X : Scheme.{u}} (M : X.Modules) (e : M ≅ structureModule X) (s : Γ(M, ⊤))

/-- A section generating everywhere has a unit scalar coordinate in an actual frame. -/
theorem sectionFrameCoordinate_isUnit_of_generatorOpen
    (hs : sectionGeneratorOpen M s = ⊤) :
    IsUnit (show Γ(X, ⊤) from e.hom.app ⊤ s) := by
  let _ := sectionGeneratorOpen_app_isIso M s ⊤ hs.ge
  obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso
    ((globalSectionHom M s).app ⊤)).surjective (e.inv.app ⊤ (1 : Γ(X, ⊤)))
  change Γ(X, ⊤) at a
  have hg : (globalSectionHom M s).app ⊤ a = a • s := by
    change a • M.presheaf.map (𝟙 (op ⊤)) s = a • s
    rw [M.presheaf.map_id, ConcreteCategory.id_apply]
  rw [hg] at ha
  have he := congrArg (fun t => e.hom.app ⊤ t) ha
  rw [Hom.app_smul] at he
  have hu : (show Γ(X, ⊤) from e.hom.app ⊤ (e.inv.app ⊤ (1 : Γ(X, ⊤)))) = 1 :=
    congrArg (fun f => f.app ⊤ (1 : Γ(X, ⊤))) e.inv_hom_id
  exact isUnit_iff_exists_inv.mpr ⟨a, (mul_comm _ _).trans (he.trans hu)⟩

end FLT.Mazur.FCurve
