/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedBaseChangeIso
public import FLT.Mazur.PolygonCompleteSmoothOriginalSubgroupCoefficient
public import FLT.Mazur.PolygonCompleteOriginalModuli
public import FLT.Mazur.PolygonCompleteSmoothFieldAtlas

/-!
# The original closed and smooth objects represent the complete family's classes

The constructed full compatible comparisons identify the original fiber classes
with the natural modular map of the actual complete family on every test scheme.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original closed full polygon and divisor define their actual ample cyclic class. -/
def completeClosedModuliClass : ampleCyclicClasses (Spec (.of K)) n :=
  Quotient.mk _ ⟨⟨_, completeClosedFiniteSubgroup K n h⟩,
    completeClosedFiniteSubgroup_isCyclic K n h, completeClosedFiniteSubgroup_isAmple K n h⟩

/-- The original closed object is precisely the closed value of the complete modular map. -/
theorem completeOriginalModuliClass_closed :
    ampleCyclicClassesPullback (completeClosedBase K) n (completeOriginalModuliClass K n h) =
      completeClosedModuliClass K n h :=
  Quotient.sound ⟨completeClosedSubgroupIso K n h⟩

/-- The identification with the original closed object holds on every closed-fiber test. -/
theorem completeOriginalModuliMap_closed {T : Scheme} (k : T ⟶ Spec (.of K))
    (f : T ⟶ Spec (.of (PowerSeries K))) (w : f = k ≫ completeClosedBase K) :
    (completeOriginalModuliMap K n h).app (Opposite.op T) (ULift.up f) =
      ampleCyclicClassesPullback k n (completeClosedModuliClass K n h) :=
  Quotient.sound ⟨completeClosedBaseChangeSubgroupIso K n h k f w⟩

variable (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
local notation "b" => Spec.map (CommRingCat.ofHom a)

/-- The pre-existing original smooth field object is the actual complete-family fiber class. -/
theorem completeOriginalModuliClass_smooth :
    ampleCyclicClassesPullback b n (completeOriginalModuliClass K n h) =
      completeFieldModuliClass K n h L a ha p q hs :=
  Quotient.sound ⟨completeSmoothOriginalSubgroupIso K n h L a ha p q hs⟩

/-- Every test of the original smooth field object retains the same complete-family class. -/
theorem completeOriginalModuliMap_smooth {T : Scheme} (k : T ⟶ Spec (.of L)) :
    (completeOriginalModuliMap K n h).app (Opposite.op T) (ULift.up (k ≫ b)) =
      ampleCyclicClassesPullback k n (completeFieldModuliClass K n h L a ha p q hs) := by
  change ampleCyclicClassesPullback (k ≫ b) n (completeOriginalModuliClass K n h) = _
  rw [ampleCyclicClassesPullback_comp]
  change ampleCyclicClassesPullback k n
    (ampleCyclicClassesPullback b n (completeOriginalModuliClass K n h)) = _
  rw [completeOriginalModuliClass_smooth]

end FLT.Mazur.PolygonInfinitesimalStages
