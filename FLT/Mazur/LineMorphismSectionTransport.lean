/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineMorphismTensorSection

/-!
# Transporting the tensor section of an original line morphism

Changing the source and target by specified isomorphisms transports the
representing section by the target isomorphism and the inverse source dual.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
universe u
namespace FLT.Mazur.FCurve
open ModuleSheafTensor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] tensor
variable {X : Scheme.{u}} {L L' M M' : X.Modules}
  (hL : LocallyFreeRankOne L) (hL' : LocallyFreeRankOne L')
  (e : L ≅ L') (d : M ≅ M')

/-- Canonical inverse biduality is natural in the specified source isomorphism. -/
theorem lineBidual_inv_transport :
    (moduleSheafDualIso _ (moduleSheafDualIso L e).symm).hom ≫
        (lineSheafBidualIso hL).inv =
      (lineSheafBidualIso hL').inv ≫ e.inv := by
  apply (cancel_epi (lineSheafBidualIso hL').hom).mp
  apply (cancel_mono (lineSheafBidualIso hL).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Iso.hom_inv_id_assoc, Category.comp_id]
  exact moduleSheafBidual_naturality e.inv

/-- Both original line isomorphisms transport the actual representing tensor section. -/
theorem lineMorphismSectionEquiv_transport (a : L ⟶ M) :
    lineMorphismSectionEquiv hL' M' (e.inv ≫ a ≫ d.hom) =
      (map d.hom (moduleSheafDualIso L e).inv).app ⊤
        (lineMorphismSectionEquiv hL M a) := by
  rw [lineMorphismSectionEquiv_apply, lineMorphismSectionEquiv_apply]
  rw [show map d.hom (moduleSheafDualIso L e).inv =
      map (𝟙 M) (moduleSheafDualIso L e).inv ≫ map d.hom (𝟙 _) by
    rw [← map_comp, Category.id_comp, Category.comp_id]]
  rw [Hom.comp_app, ConcreteCategory.comp_apply]
  have ht := lineHomSectionEquiv_transport hL.dual hL'.dual
    (moduleSheafDualIso L e).symm M ((lineSheafBidualIso hL).inv ≫ a)
  simp only [Iso.symm_hom] at ht
  rw [← ht, ← lineHomSectionEquiv_naturality]
  congr 1
  simpa only [Category.assoc] using congrArg
    (fun b ↦ b ≫ a ≫ d.hom) (lineBidual_inv_transport hL hL' e).symm

end FLT.Mazur.FCurve
