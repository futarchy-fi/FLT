/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSheafBidual
public import FLT.Mazur.LineSectionZeroDivisor
public import FLT.Mazur.DivisorSectionExact

/-!
# Recovering the actual section from its Cartier zero ideal

Canonical biduality makes the recovery preserve the section, not just the
underlying line sheaf. Dualizing the canonical Cartier section also recovers
the original ideal embedding.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

variable {X : Scheme.{0}} {L : X.Modules}

/-- Dualizing evaluation recovers the original section through canonical biduality. -/
lemma lineSectionEvaluation_bidual (s : Γ(L, ⊤)) :
    moduleSheafDualUnitIso.inv ≫ moduleSheafDualMap _ (lineSectionEvaluation s) =
      globalSectionHom L s ≫ moduleSheafBidual L := by
  rw [lineSectionEvaluation, moduleSheafDualMap_comp, ← Category.assoc,
    ← moduleSheafBidual_unit, moduleSheafBidual_naturality]

/-- The canonical recovery uses the evaluation-defined inverse bidual map. -/
def lineSectionZeroDivisorCanonicalIso (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤))
    [Mono (globalSectionHom L s)] :
    divisorLineBundle (lineSectionZeroIdeal hL s)
      (lineSectionZeroIdeal_effectiveCartier hL s) ≅ L :=
  moduleSheafDualIso _ (lineSectionZeroIdealDualIso hL s) ≪≫ (lineSheafBidualIso hL).symm

/-- Recovery carries the canonical divisor map to the original section map. -/
@[reassoc]
lemma lineSectionZeroDivisorCanonicalIso_section (hL : LocallyFreeRankOne L)
    (s : Γ(L, ⊤)) [Mono (globalSectionHom L s)] :
    divisorSectionMap (lineSectionZeroIdeal_effectiveCartier hL s) ≫
      (lineSectionZeroDivisorCanonicalIso hL s).hom = globalSectionHom L s := by
  have he : divisorSectionMap (lineSectionZeroIdeal_effectiveCartier hL s) ≫
      (moduleSheafDualIso _ (lineSectionZeroIdealDualIso hL s)).hom =
        globalSectionHom L s ≫ moduleSheafBidual L := by
    change (moduleSheafDualUnitIso.inv ≫ moduleSheafDualMap _ (idealModuleι _)) ≫
      moduleSheafDualMap _ (lineSectionZeroIdealDualIso hL s).hom = _
    rw [Category.assoc, ← moduleSheafDualMap_comp, lineSectionZeroIdealDualIso_comp,
      lineSectionEvaluation_bidual]
  change _ ≫ ((moduleSheafDualIso _ (lineSectionZeroIdealDualIso hL s)).hom ≫
    (lineSheafBidualIso hL).inv) = _
  rw [← Category.assoc, he, Category.assoc]
  change globalSectionHom L s ≫ (lineSheafBidualIso hL).hom ≫
    (lineSheafBidualIso hL).inv = _
  simp only [Iso.hom_inv_id, Category.comp_id]

/-- The recovered global section is exactly the input section. -/
lemma lineSectionZeroDivisorCanonicalIso_apply (hL : LocallyFreeRankOne L)
    (s : Γ(L, ⊤)) [Mono (globalSectionHom L s)] :
    (lineSectionZeroDivisorCanonicalIso hL s).hom.app ⊤
      (divisorSection (lineSectionZeroIdeal_effectiveCartier hL s) ⊤) = s := by
  have h := congrArg (fun f ↦ f.app ⊤ (1 : Γ(X, ⊤)))
    (lineSectionZeroDivisorCanonicalIso_section hL s)
  exact h.trans (globalSectionHom_top L s)

/-- The global section morphism associated to a canonical section is its canonical map. -/
lemma globalSectionHom_divisorSection {I : X.IdealSheafData} (hI : EffectiveCartier I) :
    globalSectionHom (divisorLineBundle I hI) (divisorSection hI ⊤) =
      divisorSectionMap hI :=
  globalSection_hom_ext _ _ (globalSectionHom_top _ _)

/-- Canonical biduality takes the dual evaluation of a Cartier section to the ideal inclusion. -/
@[reassoc]
lemma divisorSectionEvaluation_bidual {I : X.IdealSheafData} (hI : EffectiveCartier I) :
    moduleSheafBidual (idealModule I) ≫ lineSectionEvaluation (divisorSection hI ⊤) =
      idealModuleι I := by
  change moduleSheafBidual (idealModule I) ≫
    moduleSheafDualMap _ (globalSectionHom (divisorLineBundle I hI)
      (divisorSection hI ⊤)) ≫ moduleSheafDualUnitIso.hom = _
  rw [globalSectionHom_divisorSection, divisorSectionMap,
    moduleSheafDualMap_comp, ← Category.assoc, ← Category.assoc,
    moduleSheafBidual_naturality]
  rw [Category.assoc, Category.assoc, moduleSheafBidual_unit]
  change idealModuleι I ≫ moduleSheafDualUnitIso.inv ≫
    (moduleSheafDualIso _ (moduleSheafDualUnitIso (X := X))).hom ≫
    (moduleSheafDualIso _ (moduleSheafDualUnitIso (X := X))).inv ≫
    moduleSheafDualUnitIso.hom = _
  simp only [Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]

end FLT.Mazur.FCurve
