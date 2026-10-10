/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineTensorSectionEquiv

/-!
# Tensor section transport under actual base-line isomorphisms

The intrinsic dual evaluation commutes with simultaneous transport of a
line and its dual. Consequently the section correspondence retains the
actual tensor isomorphism when the twisting line changes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleSheafTensor
attribute [local irreducible] tensor
variable {X : Scheme.{u}} {B C : X.Modules} (e : B ≅ C)

/-- Simultaneous transport of a line and its dual preserves intrinsic evaluation. -/
lemma dualEvaluation_congr :
    (congr (moduleSheafDualIso B e).symm e).hom ≫ moduleSheafDualEvaluation C =
      moduleSheafDualEvaluation B := by
  change map (moduleSheafDualMap C e.inv) e.hom ≫ _ = _
  rw [show map (moduleSheafDualMap C e.inv) e.hom =
      map (𝟙 _) e.hom ≫ map (moduleSheafDualMap C e.inv) (𝟙 C) by
    rw [← map_comp]; simp only [Category.id_comp, Category.comp_id]]
  rw [Category.assoc, moduleSheafDualEvaluation_naturality,
    ← Category.assoc, ← map_comp]
  simp only [Category.id_comp, Iso.hom_inv_id, map_id, Category.id_comp]

/-- Inverse evaluations retain the same actual line transport. -/
lemma dualCoevaluation_congr (hB : LocallyFreeRankOne B) (hC : LocallyFreeRankOne C) :
    (lineSheafDualEvaluationIso hB).inv ≫ (congr (moduleSheafDualIso B e).symm e).hom =
      (lineSheafDualEvaluationIso hC).inv := by
  apply (cancel_mono (lineSheafDualEvaluationIso hC).hom).mp
  rw [Category.assoc]
  change (lineSheafDualEvaluationIso hB).inv ≫
    ((congr (moduleSheafDualIso B e).symm e).hom ≫ moduleSheafDualEvaluation C) = _
  rw [dualEvaluation_congr]
  exact (lineSheafDualEvaluationIso hB).inv_hom_id.trans
    (lineSheafDualEvaluationIso hC).inv_hom_id.symm

/-- Changing the twisting line transports the original section by the actual tensor map. -/
lemma lineHomSectionEquiv_sourceIso (L : X.Modules)
    (hB : LocallyFreeRankOne B) (hC : LocallyFreeRankOne C)
    (a : moduleSheafDual B ⟶ L) :
    lineHomSectionEquiv L hC ((moduleSheafDualIso B e).hom ≫ a) =
      (map (𝟙 L) e.hom).app ⊤ (lineHomSectionEquiv L hB a) := by
  apply (globalSectionHomEquiv _).injective
  change globalSectionHom _ _ = globalSectionHom _ _
  rw [← globalSectionHom_naturality, lineHomSectionEquiv_hom,
    lineHomSectionEquiv_hom, ← dualCoevaluation_congr e hB hC]
  rw [Category.assoc, Category.assoc]
  congr 1
  change map (moduleSheafDualIso B e).inv e.hom ≫
    map ((moduleSheafDualIso B e).hom ≫ a) (𝟙 C) = _
  rw [← map_comp, ← map_comp]
  simp only [Iso.inv_hom_id_assoc, Category.comp_id, Category.id_comp]

end FLT.Mazur.FCurve
