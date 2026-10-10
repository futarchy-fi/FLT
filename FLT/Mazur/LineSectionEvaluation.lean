/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NonzeroLineSectionExact
public import FLT.Mazur.LineSheafDualEvaluation
public import FLT.Mazur.ModuleSheafTensorAssociator

/-!
# Evaluation on an actual line section

Dualizing the section map gives the morphism from the dual line to the
structure sheaf whose image is its zero ideal. A tensor calculation proves
that this morphism is injective whenever the original section map is.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite
open Scheme.Modules

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

attribute [local irreducible] ModuleSheafTensor.tensor

open ModuleSheafTensor ModuleSheafTensorAssociator

variable {X : Scheme.{u}} {L : X.Modules}

/-- The intrinsic evaluation at a global section, as a morphism of sheaves. -/
def lineSectionEvaluation (s : Γ(L, ⊤)) : moduleSheafDual L ⟶ structureModule X :=
  moduleSheafDualMap (structureModule X) (globalSectionHom L s) ≫ moduleSheafDualUnitIso.hom

/-- Evaluation on each open pairs with the restriction of the original section. -/
lemma lineSectionEvaluation_app (s : Γ(L, ⊤)) (U : X.Opens)
    (φ : Γ(moduleSheafDual L, U)) :
    (lineSectionEvaluation s).app U φ =
      moduleDualEval L U φ (L.presheaf.map U.leTop.op s) := by
  change moduleDualEval (structureModule X) U
    ((restrictFunctor U.ι).map (globalSectionHom L s) ≫ φ) (1 : Γ(X, U)) = _
  rw [moduleDualEval_precomp]
  change moduleDualEval L U φ ((1 : Γ(X, U)) • L.presheaf.map U.leTop.op s) = _
  rw [one_smul]

/-- Tensoring the original section with the dual realizes precisely evaluation. -/
lemma lineSectionEvaluation_tensor (s : Γ(L, ⊤)) :
    (leftUnitor (moduleSheafDual L)).hom ≫ lineSectionEvaluation s =
      ModuleSheafTensor.map (globalSectionHom L s) (𝟙 (moduleSheafDual L)) ≫
        (comm L (moduleSheafDual L)).hom ≫ moduleSheafDualEvaluation L := by
  apply ModuleSheafTensor.hom_ext
  intro U r φ
  change Γ(X, U) at r
  change (lineSectionEvaluation s).app U
      ((leftUnitor (moduleSheafDual L)).hom.app U
        (pure (structureModule X) (moduleSheafDual L) U r φ)) =
    (moduleSheafDualEvaluation L).app U ((comm L (moduleSheafDual L)).hom.app U
      ((ModuleSheafTensor.map (globalSectionHom L s) (𝟙 (moduleSheafDual L))).app U
        (pure (structureModule X) (moduleSheafDual L) U r φ)))
  rw [ModuleSheafTensor.map_pure, Hom.id_app, ConcreteCategory.id_apply,
    comm_hom_pure, moduleSheafDualEvaluation_pure]
  have hu : (leftUnitor (moduleSheafDual L)).hom.app U
      (pure (structureModule X) (moduleSheafDual L) U r φ) = r • φ :=
    leftUnitor_pure (moduleSheafDual L) U r φ
  rw [hu, lineSectionEvaluation_app]
  rw [moduleDualEval_smul]
  change r * moduleDualEval L U φ (L.presheaf.map U.leTop.op s) =
    moduleDualEval L U φ (r • L.presheaf.map U.leTop.op s)
  exact ((moduleDualEval L U φ).map_smul r _).symm

/-- Regularity of the original section implies regularity of its dual evaluation. -/
theorem lineSectionEvaluation_mono (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤))
    [Mono (globalSectionHom L s)] : Mono (lineSectionEvaluation s) := by
  have h := ModuleLineTensorExact.shortExact
    (ShortComplex.cokernelSequence (globalSectionHom L s))
    { exact := ShortComplex.cokernelSequence_exact (globalSectionHom L s)
      mono_f := inferInstanceAs (Mono (globalSectionHom L s)) } (moduleSheafDual L) hL.dual
  have : Mono (ModuleSheafTensor.map (globalSectionHom L s) (𝟙 (moduleSheafDual L))) := h.mono_f
  have := moduleSheafDualEvaluation_isIso hL
  have : Mono ((leftUnitor (moduleSheafDual L)).hom ≫ lineSectionEvaluation s) := by
    rw [lineSectionEvaluation_tensor]
    infer_instance
  exact (mono_comp_iff_of_isIso (leftUnitor (moduleSheafDual L)).hom _).mp inferInstance

/-- Every nonzero section of a line on an integral scheme has injective evaluation. -/
theorem nonzero_lineSectionEvaluation_mono {X : Scheme.{0}} [IsIntegral X] {L : X.Modules}
    (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    Mono (lineSectionEvaluation s) := by
  have : Mono (globalSectionHom L s) := nonzero_globalSectionHom_mono hL s hs
  exact lineSectionEvaluation_mono hL s

end FLT.Mazur.FCurve
