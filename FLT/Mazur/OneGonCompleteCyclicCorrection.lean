/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCompleteLabelLifts
public import FLT.Mazur.KernelPowerMarkingLift

/-!
# Reducing complete cyclic marking lifts to the original formal kernel

The already constructed whole-base labels are corrected by the kernel-power
criterion. All original group equations and closed labels are retained.
Bijectivity of that power map still requires a geometric proof; it is an
explicit hypothesis here, including for prime-to-characteristic indices.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ)
variable (labels : Multiplicative (ZMod n) →*
  (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K))
variable (hpow : Function.Bijective (fun z : (completeSectionReduction K).ker ↦ z ^ n))

/-- The original cyclic label group is killed by its given index. -/
theorem cyclicLabels_pow (a : Multiplicative (ZMod n)) : a ^ n = 1 :=
  congrArg Multiplicative.ofAdd (ZModModule.char_nsmul_eq_zero n a.toAdd)

/-- Correcting the constructed smooth lifts gives a complete-base group marking. -/
def correctedCompleteMarking : Multiplicative (ZMod n) →*
    (𝟙_ (Over (Spec (.of (PowerSeries K)))) ⟶
      (relativeGroup (PowerSeries.X : PowerSeries K)).X) :=
  KernelPowerMarkingLift.marking (completeSectionReduction K) n hpow
    (closedCyclicMarking K n labels) (cyclicLabels_pow n)
    (completeLabelLift K n labels) (completeLabelLift_reduction K n labels)

/-- The corrected marking retains every prescribed original closed label. -/
@[reassoc] theorem correctedCompleteMarking_reduction (a : Multiplicative (ZMod n)) :
    completeClosedTestMap K ≫ correctedCompleteMarking K n labels hpow a =
      closedCyclicMarking K n labels a :=
  KernelPowerMarkingLift.point_reduction (completeSectionReduction K) n hpow
    (closedCyclicMarking K n labels) (cyclicLabels_pow n)
    (completeLabelLift K n labels) (completeLabelLift_reduction K n labels) a

/-- The entire corrected marking is faithful whenever the original torus marking is faithful. -/
theorem correctedCompleteMarking_injective (h : Function.Injective labels) :
    Function.Injective (correctedCompleteMarking K n labels hpow) :=
  KernelPowerMarkingLift.marking_injective (completeSectionReduction K) n hpow
    (closedCyclicMarking K n labels) (cyclicLabels_pow n)
    (completeLabelLift K n labels) (completeLabelLift_reduction K n labels)
    (closedCyclicMarking_injective K n labels h)

/-- Every complete group marking with those reductions is the constructed corrected marking. -/
theorem correctedCompleteMarking_unique
    (q : Multiplicative (ZMod n) →*
      (𝟙_ (Over (Spec (.of (PowerSeries K)))) ⟶
        (relativeGroup (PowerSeries.X : PowerSeries K)).X))
    (hq : (completeSectionReduction K).comp q = closedCyclicMarking K n labels) :
    q = correctedCompleteMarking K n labels hpow :=
  KernelPowerMarkingLift.marking_unique (completeSectionReduction K) n hpow
    (closedCyclicMarking K n labels) (cyclicLabels_pow n)
    (completeLabelLift K n labels) (completeLabelLift_reduction K n labels) q hq

end FLT.Mazur.OneGonSmoothing
