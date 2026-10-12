/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedRotation
public import FLT.Mazur.PolygonCompleteClosedSpecialization
public import FLT.Mazur.ProperLocalFixedPoint

/-!
# The complete cyclic action has empty nonidentity fixed-point schemes

The original closed-fiber computation and properness exclude invariant
morphisms from every nonempty test scheme, over arbitrary coefficient maps.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase completeRotation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The complete rotation as an endomorphism over its actual power-series base. -/
def completeRotationOver (a : ZMod n) :
    Over.mk (exactVeroneseProjToBase K n h) ⟶ Over.mk (exactVeroneseProjToBase K n h) :=
  Over.homMk (completeRotation K n h a) (completeRotation_toBase K n h a)

/-- The actual nonidentity fixed-point scheme of the complete action is empty. -/
theorem completeRotation_equalizer_isEmpty (a : ZMod n) (ha : a ≠ 0) :
    IsEmpty (equalizer (completeRotationOver K n h a) (𝟙 _)).left := by
  let _ : IsProper (Over.mk (exactVeroneseProjToBase K n h)).hom :=
    exactVeroneseProjToBase_isProper K n h
  apply ProperLocalFixedPoint.equalizer_isEmpty (PowerSeries K)
  intro x hx
  have hr : x ∈ Set.range (completeClosedFiberInclusion K n h) := by
    rw [completeClosedFiber_range]
    exact hx
  obtain ⟨z, rfl⟩ := hr
  exact completeRotation_closed_ne_self K n h a ha z

/-- A nonempty test scheme has no invariant map into the actual complete family. -/
theorem completeRotation_comp_ne {T : Scheme} [Nonempty T]
    (p : T ⟶ exactVeroneseProj K n h) (a : ZMod n) (ha : a ≠ 0) :
    p ≫ completeRotation K n h a ≠ p := by
  intro he
  let X := Over.mk (exactVeroneseProjToBase K n h)
  let Y := Over.mk (p ≫ exactVeroneseProjToBase K n h)
  let q : Y ⟶ X := Over.homMk p rfl
  have hq : q ≫ completeRotationOver K n h a = q ≫ 𝟙 X := by
    apply Over.OverMorphism.ext
    exact he
  let _ := completeRotation_equalizer_isEmpty K n h a ha
  let j := equalizer.lift q hq
  obtain ⟨t⟩ := ‹Nonempty T›
  exact isEmptyElim (j.left t)

end FLT.Mazur.PolygonInfinitesimalStages
