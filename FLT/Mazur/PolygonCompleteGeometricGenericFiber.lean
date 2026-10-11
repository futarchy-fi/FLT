/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteGenericSmooth
public import FLT.Mazur.PolygonCompleteFiberMarkings
public import FLT.Mazur.SmoothGeometricallyReduced

/-!
# The actual geometric generic fibers are nonempty, proper, smooth and reduced

All field extensions of the original fraction field retain the original
parameter as a unit and the original marked points. Genus, connectedness
and relative dimension remain separate obligations.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (F L : Type) [Field F] [Field L] [Algebra (PowerSeries K) F]
  [IsFractionRing (PowerSeries K) F] [Algebra F L] [Algebra (PowerSeries K) L]
  [IsScalarTower (PowerSeries K) F L]

include F in
/-- Every field extension of the original generic fiber is smooth over the extension field. -/
theorem completeGeometricGenericFiber_smooth :
    Smooth (pullback.snd (exactVeroneseProjToBase K n h)
      (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) L)))) := by
  apply completeBaseChange_smooth_of_parameter_isUnit
  rw [IsScalarTower.algebraMap_apply (PowerSeries K) F L]
  apply IsUnit.map
  apply isUnit_iff_ne_zero.mpr
  simpa only [map_zero] using
    (IsFractionRing.injective (PowerSeries K) F).ne PowerSeries.X_ne_zero

include F in
/-- The actual geometric generic fiber has all four stated properties without new hypotheses. -/
theorem completeGeometricGenericFiber_geometry :
    let g := Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) L))
    Nonempty ↥(pullback (exactVeroneseProjToBase K n h) g) ∧
      IsProper (pullback.snd (exactVeroneseProjToBase K n h) g) ∧
      Smooth (pullback.snd (exactVeroneseProjToBase K n h) g) ∧
      IsReduced (pullback (exactVeroneseProjToBase K n h) g) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) L))
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ := completeGeometricGenericFiber_smooth K n h F L
  exact ⟨completeFiber_nonempty K n h g, inferInstance, inferInstance,
    Approximation.isReduced_of_smooth_field (pullback.snd (exactVeroneseProjToBase K n h) g)⟩

/-- The actual generic family has geometrically reduced fibers. -/
theorem completeGenericFiber_geometricallyReduced :
    GeometricallyReduced (pullback.snd (exactVeroneseProjToBase K n h)
      (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries K) F)))) := by
  let _ := completeGenericFiber_smooth K n h F
  exact Approximation.geometricallyReduced_of_smooth _

end FLT.Mazur.PolygonInfinitesimalStages
