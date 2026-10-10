/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSheafEvaluationBalance
public import FLT.Mazur.LineSectionCanonicalRecovery

/-!
# Compatibility of tensor-inverse recovery with canonical evaluation

The explicit tensor-inverse comparison equals the inverse canonical bidual
map. Consequently the original Cartier recovery isomorphism preserves the
canonical section, without changing its existing definition.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

open ModuleSheafTensor ModuleSheafTensorAssociator

attribute [local irreducible] ModuleSheafTensor.tensor

variable {X : Scheme.{u}}

/-- Contracting a tensor inverse comparison cancels its coevaluation factors. -/
lemma tensorInverseComparison_contract {L N K : X.Modules}
    (e : tensor N L ≅ structureModule X) (d : tensor K N ≅ structureModule X) :
    (congr (Iso.refl K) e).hom ≫ (rightUnitor K).hom ≫
      (tensorInverseComparison e d).hom =
    (associator K N L).inv ≫ (congr d (Iso.refl L)).hom ≫ (leftUnitor L).hom := by
  change (congr (Iso.refl K) e).hom ≫ (rightUnitor K).hom ≫
    (rightUnitor K).inv ≫ (congr (Iso.refl K) e).inv ≫
    (associator K N L).inv ≫ (congr d (Iso.refl L)).hom ≫ (leftUnitor L).hom = _
  simp only [Iso.hom_inv_id_assoc]

/-- Pairing the inverse bidual image with a functional recovers the double-dual pairing. -/
lemma lineSheafBidualIso_inv_eval {L : X.Modules} (hL : LocallyFreeRankOne L)
    (U : X.Opens) (k : Γ(moduleSheafDual (moduleSheafDual L), U))
    (φ : Γ(moduleSheafDual L, U)) :
    moduleDualEval L U φ ((lineSheafBidualIso hL).inv.app U k) =
      moduleDualEval (moduleSheafDual L) U k φ := by
  rw [← moduleSheafBidual_eval]
  have he := congrArg (fun f ↦ f.app U k) (lineSheafBidualIso hL).inv_hom_id
  change (moduleSheafBidual L).app U ((lineSheafBidualIso hL).inv.app U k) = k at he
  rw [he]

/-- The explicit tensor comparison is the evaluation-compatible inverse bidual map. -/
theorem lineSheafDoubleDualIso_eq {L : X.Modules} (hL : LocallyFreeRankOne L) :
    lineSheafDoubleDualIso hL = (lineSheafBidualIso hL).symm := by
  apply Iso.ext
  apply (cancel_epi ((congr (Iso.refl (moduleSheafDual (moduleSheafDual L)))
    (lineSheafDualEvaluationIso hL)).hom ≫
      (rightUnitor (moduleSheafDual (moduleSheafDual L))).hom)).mp
  change _ ≫ (tensorInverseComparison (lineSheafDualEvaluationIso hL)
    (lineSheafDualEvaluationIso hL.dual)).hom = _
  rw [Category.assoc, tensorInverseComparison_contract]
  apply right_hom_ext
  intro U k φ s
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, associator_inv_pure,
    ModuleSheafTensor.congr, ModuleSheafTensor.map_pure, Iso.refl_hom, Hom.id_app,
    ConcreteCategory.id_apply, lineSheafDualEvaluationIso, asIso_hom,
    moduleSheafDualEvaluation_pure]
  have hl : (leftUnitor L).hom.app U
      (pure (structureModule X) L U (moduleDualEval (moduleSheafDual L) U k φ) s) =
        moduleDualEval (moduleSheafDual L) U k φ • s :=
    leftUnitor_pure L U (moduleDualEval (moduleSheafDual L) U k φ) s
  have hr : (rightUnitor (moduleSheafDual (moduleSheafDual L))).hom.app U
      (pure (moduleSheafDual (moduleSheafDual L)) (structureModule X) U k
        (moduleDualEval L U φ s)) = moduleDualEval L U φ s • k :=
    rightUnitor_pure (moduleSheafDual (moduleSheafDual L)) U (moduleDualEval L U φ s) k
  have hb := lineSheafEvaluation_balance hL U φ ((lineSheafBidualIso hL).inv.app U k) s
  rw [lineSheafBidualIso_inv_eval] at hb
  exact hl.trans (hb.trans (((lineSheafBidualIso hL).inv.app_smul
    (moduleDualEval L U φ s) k).symm.trans
      (congrArg ((lineSheafBidualIso hL).inv.app U) hr.symm)))

variable {X : Scheme.{0}} {L : X.Modules}

/-- The earlier tensor-based Cartier recovery is the canonical section-preserving recovery. -/
theorem lineSectionZeroDivisorLineIso_eq (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤))
    [Mono (globalSectionHom L s)] :
    lineSectionZeroDivisorLineIso hL s = lineSectionZeroDivisorCanonicalIso hL s := by
  unfold lineSectionZeroDivisorLineIso lineSectionZeroDivisorCanonicalIso
  rw [lineSheafDoubleDualIso_eq]

/-- The original recovery map carries the actual canonical divisor section to the input map. -/
@[reassoc]
lemma lineSectionZeroDivisorLineIso_section (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤))
    [Mono (globalSectionHom L s)] :
    divisorSectionMap (lineSectionZeroIdeal_effectiveCartier hL s) ≫
      (lineSectionZeroDivisorLineIso hL s).hom = globalSectionHom L s := by
  rw [lineSectionZeroDivisorLineIso_eq, lineSectionZeroDivisorCanonicalIso_section]

end FLT.Mazur.FCurve
