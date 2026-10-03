/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedLineProjectionFormula
public import FLT.Mazur.PolygonBranchDifferenceSheaf
/-!
# Projection formula with structure-sheaf coefficients

Identify the tensor of a direct-image structure sheaf with a line with the
direct image of its pullback. Pure-section and adjunction-unit formulas
fix the maps used in the line-valued normalization sequence.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve.LineStructureProjection
open ModuleSheafTensor StructureDirectImage
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules) (hL : LocallyFreeRankOne L)
/-- The projection comparison followed by the structure-sheaf tensor unitor. -/
def iso : tensor (image f) L ≅ (pushforward f).obj ((pullback f).obj L) :=
  (ClosedLineProjectionFormula.projectionIso f (structureModule X) L hL).symm ≪≫
    (pushforward f).mapIso (leftUnitor ((pullback f).obj L))
/-- A projected pure tensor is multiplication by the pulled-back line section. -/
lemma iso_pure (U : Y.Opens) (r : Γ(X, f ⁻¹ᵁ U)) (l : Γ(L, U)) :
    (iso f L hL).hom.app U (pure (image f) L U r l) =
      (r : Γ(X, f ⁻¹ᵁ U)) •
        (show Γ((pullback f).obj L, f ⁻¹ᵁ U) from
          ((pullbackPushforwardAdjunction f).unit.app L).app U l) := by
  change (leftUnitor ((pullback f).obj L)).hom.app (f ⁻¹ᵁ U)
    ((ClosedLineProjectionFormula.comparison f (structureModule X) L).app U
      (pure (image f) L U r l)) = _
  exact (congrArg ((leftUnitor ((pullback f).obj L)).hom.app (f ⁻¹ᵁ U))
    (ClosedLineProjectionFormula.comparison_pure f (structureModule X) L U r l)).trans
      (leftUnitor_pure ((pullback f).obj L) (f ⁻¹ᵁ U) r _)
/-- Tensoring the structure inclusion gives the actual pullback adjunction unit. -/
lemma unit_compatibility :
    ModuleSheafTensor.map (unitMap f) (𝟙 L) ≫ (iso f L hL).hom =
      (leftUnitor L).hom ≫ (pullbackPushforwardAdjunction f).unit.app L := by
  apply ModuleSheafTensor.hom_ext
  intro U r l
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, map_pure, Hom.id_app,
    ConcreteCategory.id_apply, iso_pure, leftUnitor_pure]
  exact (((pullbackPushforwardAdjunction f).unit.app L).val.app (op U)).hom.map_smul r l |>.symm
end FLT.Mazur.FCurve.LineStructureProjection
