/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSectionCanonicalRecovery
public import FLT.Mazur.LineSectionZeroIdealOrbits

/-!
# The two inverse constructions for Cartier sections

The canonical section of an effective Cartier ideal has precisely that full
zero ideal. Conversely, equal zero ideals of regular line sections construct
an actual isomorphism carrying one original section to the other.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

variable {X : Scheme.{0}} {L N : X.Modules}

/-- The full zero ideal of a canonical Cartier section is the original ideal. -/
theorem lineSectionZeroIdeal_divisorSection (I : X.IdealSheafData) (hI : EffectiveCartier I) :
    lineSectionZeroIdeal hI.divisorLineBundle_locallyFreeRankOne (divisorSection hI ⊤) = I := by
  have hL := hI.idealModule_locallyFreeRankOne
  have := hL.isFinitePresentation
  have := hI.divisorLineBundle_locallyFreeRankOne.dual.isFinitePresentation
  change quasicoherentImageIdeal (lineSectionEvaluation (divisorSection hI ⊤)) = I
  apply Eq.trans ?_ (quasicoherentImageIdeal_idealModuleι I)
  symm
  exact quasicoherentImageIdeal_eq_of_iso _ _ (lineSheafBidualIso hL)
    (divisorSectionEvaluation_bidual hI)

/-- A compatible dual isomorphism canonically induces an isomorphism of original lines. -/
def lineSectionDualIso (hL : LocallyFreeRankOne L) (hN : LocallyFreeRankOne N)
    (e : moduleSheafDual N ≅ moduleSheafDual L) : L ≅ N :=
  lineSheafBidualIso hL ≪≫ moduleSheafDualIso _ e ≪≫ (lineSheafBidualIso hN).symm

/-- The induced isomorphism preserves the original section morphisms. -/
lemma lineSectionDualIso_section (hL : LocallyFreeRankOne L) (hN : LocallyFreeRankOne N)
    (s : Γ(L, ⊤)) (t : Γ(N, ⊤)) (e : moduleSheafDual N ≅ moduleSheafDual L)
    (he : e.hom ≫ lineSectionEvaluation s = lineSectionEvaluation t) :
    globalSectionHom L s ≫ (lineSectionDualIso hL hN e).hom = globalSectionHom N t := by
  have hd := congrArg (fun a ↦ moduleSheafDualUnitIso.inv ≫ moduleSheafDualMap _ a) he
  rw [moduleSheafDualMap_comp, ← Category.assoc, lineSectionEvaluation_bidual,
    lineSectionEvaluation_bidual] at hd
  change globalSectionHom L s ≫
    ((lineSheafBidualIso hL).hom ≫ (moduleSheafDualIso _ e).hom ≫
      (lineSheafBidualIso hN).inv) = _
  change (globalSectionHom L s ≫ moduleSheafBidual L ≫
    moduleSheafDualMap _ e.hom) ≫ (lineSheafBidualIso hN).inv = _
  rw [← Category.assoc, hd, Category.assoc]
  change globalSectionHom N t ≫ (lineSheafBidualIso hN).hom ≫
    (lineSheafBidualIso hN).inv = _
  simp only [Iso.hom_inv_id, Category.comp_id]

/-- On global sections the induced isomorphism takes the given section to the other one. -/
lemma lineSectionDualIso_apply (hL : LocallyFreeRankOne L) (hN : LocallyFreeRankOne N)
    (s : Γ(L, ⊤)) (t : Γ(N, ⊤)) (e : moduleSheafDual N ≅ moduleSheafDual L)
    (he : e.hom ≫ lineSectionEvaluation s = lineSectionEvaluation t) :
    (lineSectionDualIso hL hN e).hom.app ⊤ s = t := by
  have h := congrArg (fun f ↦ f.app ⊤ (1 : Γ(X, ⊤)))
    (lineSectionDualIso_section hL hN s t e he)
  simpa only [Hom.comp_app, ConcreteCategory.comp_apply, globalSectionHom_top] using h

/-- Full zero ideals classify actual regular section pairs, in both directions. -/
theorem lineSectionZeroIdeal_eq_iff_iso (hL : LocallyFreeRankOne L)
    (hN : LocallyFreeRankOne N) (s : Γ(L, ⊤)) (t : Γ(N, ⊤))
    [Mono (globalSectionHom L s)] [Mono (globalSectionHom N t)] :
    lineSectionZeroIdeal hL s = lineSectionZeroIdeal hN t ↔
      ∃ e : L ≅ N, e.hom.app ⊤ s = t := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := (lineSectionZeroIdeal_eq_iff_dual_iso hN hL t s).mp h.symm
    exact ⟨lineSectionDualIso hL hN e, lineSectionDualIso_apply hL hN s t e he⟩
  · rintro ⟨e, he⟩
    exact lineSectionZeroIdeal_eq_of_iso hL hN e s t he

/-- On integral schemes it is enough for both original sections to be nonzero. -/
theorem nonzero_lineSectionZeroIdeal_eq_iff_iso [IsIntegral X]
    (hL : LocallyFreeRankOne L) (hN : LocallyFreeRankOne N)
    (s : Γ(L, ⊤)) (t : Γ(N, ⊤)) (hs : s ≠ 0) (ht : t ≠ 0) :
    lineSectionZeroIdeal hL s = lineSectionZeroIdeal hN t ↔
      ∃ e : L ≅ N, e.hom.app ⊤ s = t := by
  have := nonzero_globalSectionHom_mono hL s hs
  have := nonzero_globalSectionHom_mono hN t ht
  exact lineSectionZeroIdeal_eq_iff_iso hL hN s t

end FLT.Mazur.FCurve
