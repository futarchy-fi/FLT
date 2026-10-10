/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSectionDivisorCorrespondence
public import FLT.Mazur.DivisorLinePullback

/-!
# Pullback of the full zero ideal of a regular line section

An invertible canonical ideal comparison identifies the pulled section with
the canonical section of the pulled Cartier divisor. This proves regularity
and equality of full ideals, not just equality of supports.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y : Scheme.{0}} (f : X ⟶ Y) {L : Y.Modules}
variable (hL : LocallyFreeRankOne L) (s : Γ(L, ⊤)) [Mono (globalSectionHom L s)]
variable (hJ : EffectiveCartier ((lineSectionZeroIdeal hL s).comap f))
variable [IsIso (idealModulePullbackHom (lineSectionZeroIdeal hL s) f)]

/-- The positive pulled divisor line compares to the actual pulled coefficient line. -/
def zeroDivisorPullbackLineIso :
    divisorLineBundle ((lineSectionZeroIdeal hL s).comap f) hJ ≅ (pullback f).obj L :=
  (divisorLinePullbackIsoOfEq f (lineSectionZeroIdeal_effectiveCartier hL s) hJ rfl).symm ≪≫
    (pullback f).mapIso (lineSectionZeroDivisorCanonicalIso hL s)

/-- The comparison carries the canonical pulled-divisor map to the actual pulled section. -/
lemma zeroDivisorPullbackLineIso_section :
    divisorSectionMap hJ ≫ (zeroDivisorPullbackLineIso f hL s hJ).hom =
      globalSectionHom _ (pullGlobal f L s) := by
  let e := divisorLinePullbackIsoOfEq f
    (lineSectionZeroIdeal_effectiveCartier hL s) hJ rfl
  have he := divisorLinePullbackIsoOfEq_section f
    (lineSectionZeroIdeal_effectiveCartier hL s) hJ rfl
  change (pullback f).map (divisorSectionMap _) ≫ e.hom =
    (modulePullbackUnitIso f).hom ≫ divisorSectionMap hJ at he
  have hj : divisorSectionMap hJ ≫ e.inv =
      (modulePullbackUnitIso f).inv ≫ (pullback f).map (divisorSectionMap _) := by
    apply (cancel_epi (modulePullbackUnitIso f).hom).mp
    rw [← Category.assoc, ← he]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  change divisorSectionMap hJ ≫
    (e.inv ≫ (pullback f).map (lineSectionZeroDivisorCanonicalIso hL s).hom) = _
  rw [← Category.assoc, hj, Category.assoc, ← Functor.map_comp,
    lineSectionZeroDivisorCanonicalIso_section, globalSectionHom_pullGlobal]

include hJ in
/-- The original pulled section is regular whenever the pulled ideal remains Cartier. -/
theorem pullGlobal_regular_of_zeroIdeal :
    Mono (globalSectionHom _ (pullGlobal f L s)) := by
  rw [← zeroDivisorPullbackLineIso_section f hL s hJ]
  infer_instance

include hJ in
/-- Actual section pullback takes its full zero ideal to the ideal-sheaf comap. -/
theorem lineSectionZeroIdeal_pullGlobal :
    lineSectionZeroIdeal (hL.pullback f) (pullGlobal f L s) =
      (lineSectionZeroIdeal hL s).comap f := by
  have hs : (zeroDivisorPullbackLineIso f hL s hJ).hom.app ⊤ (divisorSection hJ ⊤) =
      pullGlobal f L s := by
    have h := congrArg (fun a ↦ a.app ⊤ (1 : Γ(X, ⊤)))
      (zeroDivisorPullbackLineIso_section f hL s hJ)
    exact h.trans (globalSectionHom_top _ _)
  exact (lineSectionZeroIdeal_eq_of_iso hJ.divisorLineBundle_locallyFreeRankOne
    (hL.pullback f) (zeroDivisorPullbackLineIso f hL s hJ)
    (divisorSection hJ ⊤) (pullGlobal f L s) hs).symm.trans
      (lineSectionZeroIdeal_divisorSection _ hJ)

end FLT.Mazur.FCurve
