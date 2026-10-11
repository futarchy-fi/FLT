/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteGeometricallyConnected

/-!
# Actual functions under arbitrary affine change of the complete polygon base

The original connected closed fiber controls functions even after a
nonreduced or non-Noetherian affine base change. The inverse of structural
pullback is evaluation along any retained original labeled marking.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S : Scheme} [IsAffine S] (s : S ⟶ Spec (.of (PowerSeries K)))

/-- Every affine change of the original complete base has exactly the base's functions. -/
theorem completeAffineFiber_appTop_bijective :
    Function.Bijective (pullback.snd (exactVeroneseProjToBase K n h) s).appTop := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ := exactVeroneseProjToBase_flat K n h
  let _ := exactVeroneseProjToBase_geometricallyReduced K n h
  let _ := exactVeroneseProjToBase_geometricallyConnected K n h
  let R := CommRingCat.of (PowerSeries K)
  let _ : IsLocalRing Γ(Spec R, ⊤) :=
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.isLocalRing
  let _ : IsNoetherianRing Γ(Spec R, ⊤) :=
    isNoetherianRing_of_ringEquiv R (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  apply LocalClosedFiberUniversalFunctions.appTop_bijective (.of_hasPullback _ _)
    (completeBaseMarking K n h ⟨0, by omega⟩) (completeBaseMarking_toBase K n h _)
  change GeometricallyConnected ((exactVeroneseProjToBase K n h).fiberToSpecResidueField _)
  infer_instance

/-- Evaluation along each actual labeled marking inverts structural pullback. -/
theorem completeAffineFiber_evaluation_inverse (i : Fin n) :
    (completeFiberMarking K n h s i).appTop ≫
      (pullback.snd (exactVeroneseProjToBase K n h) s).appTop = 𝟙 _ := by
  let _ : IsIso (pullback.snd (exactVeroneseProjToBase K n h) s).appTop :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (completeAffineFiber_appTop_bijective K n h s)
  rw [← cancel_epi (pullback.snd (exactVeroneseProjToBase K n h) s).appTop]
  rw [← Category.assoc, ← Scheme.Hom.comp_appTop, completeFiberMarking_snd]
  simp

/-- The function comparison retains both the original structure map and chosen marking. -/
def completeAffineFiberFunctionsIso (i : Fin n) :
    Γ(S, ⊤) ≅ Γ(pullback (exactVeroneseProjToBase K n h) s, ⊤) where
  hom := (pullback.snd (exactVeroneseProjToBase K n h) s).appTop
  inv := (completeFiberMarking K n h s i).appTop
  hom_inv_id := by
    rw [← Scheme.Hom.comp_appTop, completeFiberMarking_snd, Scheme.Hom.id_appTop]
  inv_hom_id := completeAffineFiber_evaluation_inverse K n h s i

end FLT.Mazur.PolygonInfinitesimalStages
