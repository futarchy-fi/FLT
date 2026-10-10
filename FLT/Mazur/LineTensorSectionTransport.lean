/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineTensorSectionEquiv

/-!
# Transport of tensor-dual sections along a line isomorphism

Changing the line factor transports the corresponding morphism by its actual
contravariant dual. This applies in particular to geometric square comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.FCurve
open ModuleSheafTensor
attribute [local irreducible] ModuleSheafTensor.tensor
variable {X : Scheme.{u}} {B C : X.Modules}
  (hB : LocallyFreeRankOne B) (hC : LocallyFreeRankOne C) (e : B ≅ C)

/-- Inverse evaluation is natural in an isomorphism of line sheaves. -/
lemma lineDualCoevaluation_transport :
    (lineSheafDualEvaluationIso hC).inv ≫ map (moduleSheafDualIso B e).hom (𝟙 C) =
      (lineSheafDualEvaluationIso hB).inv ≫ map (𝟙 (moduleSheafDual B)) e.hom := by
  have hi : congr (moduleSheafDualIso B e) (Iso.refl B) ≪≫
      lineSheafDualEvaluationIso hB =
    congr (Iso.refl (moduleSheafDual C)) e ≪≫ lineSheafDualEvaluationIso hC :=
    Iso.ext (moduleSheafDualEvaluation_naturality B e.hom)
  have hh := congrArg (fun j ↦ j ≫ map (moduleSheafDualIso B e).hom e.hom)
    (congrArg Iso.inv hi)
  simpa only [Iso.trans_inv, ModuleSheafTensor.congr, Iso.refl_inv, Category.assoc,
    ← ModuleSheafTensor.map_comp, Iso.inv_hom_id, Category.id_comp, Category.comp_id]
    using hh.symm

/-- Transporting the tensor line factor precomposes by the actual dual isomorphism. -/
lemma lineHomSectionEquiv_transport (L : X.Modules) (a : moduleSheafDual B ⟶ L) :
    lineHomSectionEquiv L hC ((moduleSheafDualIso B e).hom ≫ a) =
      (map (𝟙 L) e.hom).app ⊤ (lineHomSectionEquiv L hB a) := by
  apply (globalSectionHomEquiv _).injective
  change globalSectionHom _ _ = globalSectionHom _ _
  rw [lineHomSectionEquiv_hom, ← globalSectionHom_naturality, lineHomSectionEquiv_hom]
  have hm : map ((moduleSheafDualIso B e).hom ≫ a) (𝟙 C) =
      map (moduleSheafDualIso B e).hom (𝟙 C) ≫ map a (𝟙 C) := by
    rw [← ModuleSheafTensor.map_comp, Category.id_comp]
  rw [hm, ← Category.assoc, lineDualCoevaluation_transport hB hC e]
  simp only [Category.assoc, ← ModuleSheafTensor.map_comp, Category.id_comp,
    Category.comp_id]

/-- The inverse section correspondence retains the same contravariant dual transport. -/
lemma lineHomSectionEquiv_symm_transport (L : X.Modules) (s : Γ(tensor L B, ⊤)) :
    (lineHomSectionEquiv L hC).symm ((map (𝟙 L) e.hom).app ⊤ s) =
      (moduleSheafDualIso B e).hom ≫ (lineHomSectionEquiv L hB).symm s := by
  apply (lineHomSectionEquiv L hC).injective
  rw [Equiv.apply_symm_apply, lineHomSectionEquiv_transport hB hC e, Equiv.apply_symm_apply]

end FLT.Mazur.FCurve
