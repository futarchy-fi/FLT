/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorComplementExhaustion
public import FLT.Mazur.PolygonCompletePointFunctionNumerators

/-!
# The original marked-point complement coordinate ring

Actual tensor numerators exhaust all complement functions, so the existing
coordinate evaluation is bijective and gives an isomorphism of rings.
This statement does not assume the complement is affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve Scheme.Modules ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] {Y : Scheme}
  (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

/-- Every original complement function has a finite original pole bound. -/
theorem completeCartesianPointFunction_hasPole (i : Fin n)
    (a : divisorComplementModule q (completeCartesianMarking K n h s p q hs i).ker) :
    ∃ m, a ∈ divisorPoleSubmodule q
      (completeCartesianMarking_relativeCartier K n h s p q hs i).1 m := by
  let _ := completeCartesianPoint_isNoetherian K n h L s p q hs
  exact exists_mem_divisorPoleSubmodule
    (completeCartesianMarking_relativeCartier K n h s p q hs i).1 q a

/-- The actual coordinate evaluation reaches every regular function on the complement. -/
theorem completeCartesianPointCoordinateEvaluation_surjective (i : Fin n) :
    Function.Surjective (completeCartesianPointCoordinateEvaluation K n h L s p q hs i) := by
  intro a
  obtain ⟨m, hm⟩ := completeCartesianPointFunction_hasPole K n h L s p q hs i a
  exact completeCartesianPointPole_le_coordinateRange K n h L s p q hs i m hm

/-- The original coordinate ring is the actual ring of complement functions. -/
def completeCartesianPointCoordinateRingEquiv (i : Fin n) :
    (completeCartesianPointWeierstrass K n h L s p q hs i).toAffine.CoordinateRing ≃+*
      Γ((completeCartesianPointComplement K n h L s p q hs i).toScheme, ⊤) :=
  RingEquiv.ofBijective (completeCartesianPointCoordinateEvaluation K n h L s p q hs i)
    ⟨completeCartesianPointCoordinateEvaluation_injective K n h L s p q hs i,
      completeCartesianPointCoordinateEvaluation_surjective K n h L s p q hs i⟩

/-- The ring isomorphism retains exactly the previously constructed evaluation map. -/
theorem completeCartesianPointCoordinateRingEquiv_toRingHom (i : Fin n) :
    (completeCartesianPointCoordinateRingEquiv K n h L s p q hs i).toRingHom =
      completeCartesianPointCoordinateEvaluation K n h L s p q hs i := rfl

/-- Each actual complement function has exactly one affine coordinate representative. -/
theorem completeCartesianPoint_uniqueCoordinate (i : Fin n)
    (a : Γ((completeCartesianPointComplement K n h L s p q hs i).toScheme, ⊤)) :
    ∃! z, completeCartesianPointCoordinateEvaluation K n h L s p q hs i z = a := by
  obtain ⟨z, hz⟩ := completeCartesianPointCoordinateEvaluation_surjective K n h L s p q hs i a
  exact ⟨z, hz, fun w hw ↦ completeCartesianPointCoordinateEvaluation_injective
    K n h L s p q hs i (hw.trans hz.symm)⟩

end FLT.Mazur.PolygonInfinitesimalStages
