/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineTensorSectionPullback
public import FLT.Mazur.LineTensorSectionTransport
public import FLT.Mazur.LineSheafBidualPullback

/-!
# Actual line morphisms as tensor-dual sections

The source line itself, rather than an unidentified double dual, is retained.
The correspondence commutes with the canonical geometric pullback comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
universe u
namespace FLT.Mazur.FCurve
open ModuleSheafTensor ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] tensor tensorIso moduleSheafDualPullbackIso
variable {X Y : Scheme.{u}} {L : Y.Modules} (hL : LocallyFreeRankOne L) (M : Y.Modules)

/-- Morphisms from the original line correspond to sections of the target twisted by its dual. -/
def lineMorphismSectionEquiv : (L ⟶ M) ≃ Γ(tensor M (moduleSheafDual L), ⊤) :=
  (Iso.homCongr (lineSheafBidualIso hL) (Iso.refl M)).trans
    (lineHomSectionEquiv M hL.dual)

/-- The correspondence uses inverse canonical biduality on the original source. -/
theorem lineMorphismSectionEquiv_apply (a : L ⟶ M) :
    lineMorphismSectionEquiv hL M a =
      lineHomSectionEquiv M hL.dual ((lineSheafBidualIso hL).inv ≫ a) := by
  simp only [lineMorphismSectionEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_hom, Category.comp_id]

/-- Canonical comparison for the tensor-dual line representing actual morphisms. -/
def lineMorphismTensorPullbackIso (f : X ⟶ Y) :
    (pullback f).obj (tensor M (moduleSheafDual L)) ≅
      tensor ((pullback f).obj M) (moduleSheafDual ((pullback f).obj L)) :=
  tensorIso f M (moduleSheafDual L) ≪≫
    congr (Iso.refl _) (moduleSheafDualPullbackIso f hL)

/-- Pullback of the representing section represents pullback of the original morphism. -/
theorem lineMorphismSectionEquiv_pullback (f : X ⟶ Y) (a : L ⟶ M) :
    (lineMorphismTensorPullbackIso hL M f).hom.app ⊤
        (pullGlobal f _ (lineMorphismSectionEquiv hL M a)) =
      lineMorphismSectionEquiv (hL.pullback f) ((pullback f).obj M) ((pullback f).map a) := by
  rw [lineMorphismSectionEquiv_apply, lineMorphismSectionEquiv_apply]
  change (map (𝟙 _) (moduleSheafDualPullbackIso f hL).hom).app ⊤
    ((tensorIso f M (moduleSheafDual L)).hom.app ⊤
      (pullGlobal f _ (lineHomSectionEquiv M hL.dual _))) = _
  rw [← lineHomSectionEquiv_pullback,
    ← lineHomSectionEquiv_transport (hL.dual.pullback f) (hL.pullback f).dual]
  congr 1
  rw [Functor.map_comp]
  simpa only [Category.assoc] using congrArg
    (fun b ↦ b ≫ (pullback f).map a) (lineBidual_pullback_inv_normalized f hL)

end FLT.Mazur.FCurve
