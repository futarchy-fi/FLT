/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSheafDualTriangle

/-!
# Retaining original line isomorphisms under duality

The intrinsic bidual satisfies the evaluation triangle. For line sheaves it
identifies the dual bidual map with inverse biduality, so every isomorphism
of dual lines comes from an actual isomorphism of the original lines.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleSheafTensor
attribute [local irreducible] tensor moduleSheafBidual
variable {X : Scheme.{u}}

/-- The dual of biduality is inverse biduality on the dual line. -/
lemma lineSheafBidualIso_dual {B : X.Modules} (hB : LocallyFreeRankOne B) :
    moduleSheafDualIso B (lineSheafBidualIso hB) = (lineSheafBidualIso hB.dual).symm := by
  apply Iso.ext
  apply (cancel_epi (lineSheafBidualIso hB.dual).hom).mp
  exact (moduleSheafBidual_dual_triangle B).trans
    (lineSheafBidualIso hB.dual).hom_inv_id.symm

/-- Dual biduality on the original line is the inverse on its intrinsic dual. -/
lemma lineSheafBidualIso_dual_hom {B : X.Modules} (hB : LocallyFreeRankOne B) :
    moduleSheafDualMap B (lineSheafBidualIso hB).hom =
      (lineSheafBidualIso hB.dual).inv :=
  congrArg Iso.hom (lineSheafBidualIso_dual hB)

/-- Dual inverse biduality is forward biduality on the intrinsic dual. -/
lemma lineSheafBidualIso_dual_inv {B : X.Modules} (hB : LocallyFreeRankOne B) :
    moduleSheafDualMap _ (lineSheafBidualIso hB).inv =
      (lineSheafBidualIso hB.dual).hom :=
  congrArg Iso.inv (lineSheafBidualIso_dual hB)

/-- Recover an original line isomorphism from a contravariant dual-line isomorphism. -/
def lineIsoOfDualIso {B C : X.Modules} (hB : LocallyFreeRankOne B)
    (hC : LocallyFreeRankOne C) (a : moduleSheafDual C ≅ moduleSheafDual B) : B ≅ C :=
  lineSheafBidualIso hB ≪≫ moduleSheafDualIso _ a ≪≫ (lineSheafBidualIso hC).symm

/-- The recovered isomorphism uses the three specified original comparisons. -/
lemma lineIsoOfDualIso_hom {B C : X.Modules} (hB : LocallyFreeRankOne B)
    (hC : LocallyFreeRankOne C) (a : moduleSheafDual C ≅ moduleSheafDual B) :
    (lineIsoOfDualIso hB hC a).hom = (lineSheafBidualIso hB).hom ≫
      moduleSheafDualMap _ a.hom ≫ (lineSheafBidualIso hC).inv := rfl

attribute [local irreducible] lineIsoOfDualIso

/-- The constructed original isomorphism has exactly the given dual, not merely its orbit. -/
lemma lineIsoOfDualIso_dual {B C : X.Modules} (hB : LocallyFreeRankOne B)
    (hC : LocallyFreeRankOne C) (a : moduleSheafDual C ≅ moduleSheafDual B) :
    moduleSheafDualMap B (lineIsoOfDualIso hB hC a).hom = a.hom := by
  rw [lineIsoOfDualIso_hom, moduleSheafDualMap_comp, moduleSheafDualMap_comp]
  rw [lineSheafBidualIso_dual_inv, lineSheafBidualIso_dual_hom]
  rw [Category.assoc]
  change moduleSheafBidual (moduleSheafDual C) ≫
    moduleSheafDualMap _ (moduleSheafDualMap _ a.hom) ≫
      (lineSheafBidualIso hB.dual).inv = a.hom
  rw [← Category.assoc, moduleSheafBidual_naturality, Category.assoc]
  change a.hom ≫ (lineSheafBidualIso hB.dual).hom ≫
    (lineSheafBidualIso hB.dual).inv = a.hom
  rw [Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.FCurve
