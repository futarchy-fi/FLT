/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicModuliBridge

/-!
# Original modular classes on arbitrary normalized-chart overlaps

Two parameters representing pullbacks of the same original class agree as
modular classes on every common test. Auxiliary labels need not agree.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
open GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- Restriction of a full normalized parameter is actual modular base change. -/
theorem cyclicNormalizedSliceModuliMap_pullback {T U : Scheme}
    (g : U ⟶ T) (p : T ⟶ cyclicNormalizedSlice n) :
    (cyclicNormalizedSliceModuliMap n).app (Opposite.op U) (ULift.up (g ≫ p)) =
      ampleCyclicClassesPullback g n
        ((cyclicNormalizedSliceModuliMap n).app (Opposite.op T) (ULift.up p)) := by
  exact congrArg (fun k : ULift.{1} (T ⟶ cyclicNormalizedSlice n) ⟶
    ampleCyclicClasses U n ↦ k (ULift.up p))
      ((cyclicNormalizedSliceModuliMap n).naturality g.op)

/-- Arbitrary common tests of two original parameters have the same modular class. -/
theorem cyclicNormalizedSliceModuliMap_overlap {S T U V : Scheme}
    (c : ampleCyclicClasses S n) (f : T ⟶ S) (g : U ⟶ S)
    (p : T ⟶ cyclicNormalizedSlice n) (q : U ⟶ cyclicNormalizedSlice n)
    (hp : (cyclicNormalizedSliceModuliMap n).app (Opposite.op T) (ULift.up p) =
      ampleCyclicClassesPullback f n c)
    (hq : (cyclicNormalizedSliceModuliMap n).app (Opposite.op U) (ULift.up q) =
      ampleCyclicClassesPullback g n c)
    (a : V ⟶ T) (b : V ⟶ U) (hab : a ≫ f = b ≫ g) :
    (cyclicNormalizedSliceModuliMap n).app (Opposite.op V) (ULift.up (a ≫ p)) =
      (cyclicNormalizedSliceModuliMap n).app (Opposite.op V) (ULift.up (b ≫ q)) := by
  rw [cyclicNormalizedSliceModuliMap_pullback, cyclicNormalizedSliceModuliMap_pullback,
    hp, hq]
  exact (congrFun (ampleCyclicClassesPullback_comp f a n) c).symm.trans
    ((congrArg (fun k ↦ ampleCyclicClassesPullback k n c) hab).trans
      (congrFun (ampleCyclicClassesPullback_comp g b n) c))

end FLT.Mazur.UniversalWeierstrass
