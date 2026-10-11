/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCoefficientFinite
public import FLT.Mazur.PolygonCompleteCoefficientStageKernel
public import FLT.Mazur.ProperLocalAdicFiniteIso

/-!
# The complete coefficient comparison is an actual isomorphism

Finiteness and the original cartesian adic identities recover the global
inverse. The independently chosen Veronese steps remain unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj
variable {K L : Type} [Field K] [Field L] (f : K →+* L) (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original finite comparison to the actual coefficient pullback is invertible. -/
theorem completeCoefficientComparison_isIso : IsIso (completeCoefficientComparison f n h) := by
  let _ := completeCoefficientComparison_isFinite f n h
  let _ := exactVeroneseProjToBase_isProper K n h
  let g := pullback.snd (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom (PowerSeries.map f)))
  let _ := LocallyOfFiniteType.isLocallyNoetherian g
  exact ProperLocalAdic.isIso_of_cartesian_identities (completeCoefficientComparison f n h) g
    (BaseAdicThickening.baseIdeal (.of (PowerSeries L)) (parameterIdeal L))
    (completeParameterBaseIdeal_closedPoint L) (fun m ↦ (family L m n h).left)
    (originalStageToCompatibleProj L n h)
    (originalStageToCoefficientPullback_isClosedImmersion f n h)
    (originalStageToCoefficientPullback_ker f n h)
    (completeCoefficientComparison_stage_isPullback f n h)

/-- The global coefficient isomorphism uses the previously constructed comparison map. -/
def completeCoefficientPullbackIso : exactVeroneseProj L n h ≅
    pullback (exactVeroneseProjToBase K n h)
      (Spec.map (CommRingCat.ofHom (PowerSeries.map f))) := by
  let _ := completeCoefficientComparison_isIso f n h
  exact asIso (completeCoefficientComparison f n h)

/-- The actual complete coefficient structural square is cartesian. -/
theorem completeCoefficientProjMap_isPullback :
    IsPullback (completeCoefficientProjMap f n h) (exactVeroneseProjToBase L n h)
      (exactVeroneseProjToBase K n h)
      (Spec.map (CommRingCat.ofHom (PowerSeries.map f))) :=
  IsPullback.of_iso_pullback ⟨completeCoefficientProjMap_toBase f n h⟩
    (completeCoefficientPullbackIso f n h) (completeCoefficientComparison_fst f n h)
    (completeCoefficientComparison_snd f n h)

end FLT.Mazur.PolygonInfinitesimalStages
