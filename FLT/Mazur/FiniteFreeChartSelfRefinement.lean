/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeInheritedChartTransitions

/-!
# Identity refinement of original finite free frames

Self-refinement is idempotent by restriction coherence and injective by the
faithfulness of restriction along an identity open immersion. It is therefore
exactly the original frame, including all canonical restriction comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.FiniteFreeChartTransitions

/-- Refining an original finite free frame to its own open leaves it unchanged. -/
lemma refineChart_self {X : Scheme.{u}} (M : X.Modules) {U : X.Opens} {ι : Type u}
    (e : M.restrict U.ι ≅ SheafOfModules.free ι) : refineChart M le_rfl e = e := by
  have hh : X.homOfLE (show U ≤ U from le_rfl) = 𝟙 U.toScheme := by
    apply (cancel_mono U.ι).mp
    simp
  have hf : (restrictFunctor (X.homOfLE (show U ≤ U from le_rfl))).Faithful := by
    exact Functor.Faithful.of_iso
      (restrictFunctorCongr hh ≪≫ restrictFunctorId).symm
  have he := congrArg Iso.hom (refineChart_trans M (show U ≤ U from le_rfl) le_rfl e)
  apply Iso.ext
  apply (restrictFunctor (X.homOfLE (show U ≤ U from le_rfl))).map_injective
  dsimp only [refineChart, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at he
  simpa only [refineChart, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Category.assoc, cancel_epi, cancel_mono] using he

end FLT.Mazur.FiniteFreeChartTransitions
