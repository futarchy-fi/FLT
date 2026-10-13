/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointCanonicalBasis
public import FLT.Mazur.PolygonCompletePointSpecifiedBasis

/-!
# Canonically normalized low-pole bases over the complete base

The degree-one vector is the original divisor section. The next two vectors
are the already constructed normalized integral lifts in the common frame.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Module
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The canonical section and the actual order-two lift form an integral basis. -/
def completePointTwoCanonicalBasis (i : Fin n) :
    Basis (Unit ⊕ Unit) Γ(Spec (.of (PowerSeries K)), ⊤)
      (ModuleRingH (exactVeroneseProjToBase K n h).appTop.hom
        (tensorPower (completePointLine K n h i) 2) 0) :=
  completePointSpecifiedBasis K n h i 1 (completePointOneCanonicalBasis K n h i)
    (completePointPoleLift K n h i 0) (completePointPoleLift_coefficient K n h i 0)

/-- The order-three lift extends the same canonically normalized integral basis. -/
def completePointThreeCanonicalBasis (i : Fin n) :
    Basis ((Unit ⊕ Unit) ⊕ Unit) Γ(Spec (.of (PowerSeries K)), ⊤)
      (ModuleRingH (exactVeroneseProjToBase K n h).appTop.hom
        (tensorPower (completePointLine K n h i) 3) 0) :=
  completePointSpecifiedBasis K n h i 2 (completePointTwoCanonicalBasis K n h i)
    (completePointPoleLift K n h i 1) (completePointPoleLift_coefficient K n h i 1)

/-- The first order-two vector retains the actual divisor inclusion. -/
theorem completePointTwoCanonicalBasis_old (i : Fin n) (j : Unit) :
    completePointTwoCanonicalBasis K n h i (Sum.inl j) =
      divisorPowerRingStep (exactVeroneseProjToBase K n h).appTop.hom
        (completeBaseMarking_relativeCartier K n h i).1 1
        (completePointOneCanonicalBasis K n h i j) :=
  completePointSpecifiedBasis_old _ _ _ _ _ _ _ _ j

/-- The second order-two vector is the previously constructed normalized lift. -/
theorem completePointTwoCanonicalBasis_new (i : Fin n) :
    completePointTwoCanonicalBasis K n h i (Sum.inr ()) = completePointPoleLift K n h i 0 :=
  completePointSpecifiedBasis_new _ _ _ _ _ _ _ _

/-- Both old vectors enter degree three through the original divisor inclusion. -/
theorem completePointThreeCanonicalBasis_old (i : Fin n) (j : Unit ⊕ Unit) :
    completePointThreeCanonicalBasis K n h i (Sum.inl j) =
      divisorPowerRingStep (exactVeroneseProjToBase K n h).appTop.hom
        (completeBaseMarking_relativeCartier K n h i).1 2
        (completePointTwoCanonicalBasis K n h i j) :=
  completePointSpecifiedBasis_old _ _ _ _ _ _ _ _ j

/-- The final order-three vector is the previously constructed normalized lift. -/
theorem completePointThreeCanonicalBasis_new (i : Fin n) :
    completePointThreeCanonicalBasis K n h i (Sum.inr ()) = completePointPoleLift K n h i 1 :=
  completePointSpecifiedBasis_new _ _ _ _ _ _ _ _

/-- The initial order-three vector retains the canonical section and both inclusions. -/
theorem completePointThreeCanonicalBasis_one (i : Fin n) :
    completePointThreeCanonicalBasis K n h i (Sum.inl (Sum.inl ())) =
      divisorPowerRingStep (exactVeroneseProjToBase K n h).appTop.hom
        (completeBaseMarking_relativeCartier K n h i).1 2
        (divisorPowerRingStep (exactVeroneseProjToBase K n h).appTop.hom
          (completeBaseMarking_relativeCartier K n h i).1 1
          (completePointOneCanonicalBasis K n h i ())) := by
  rw [completePointThreeCanonicalBasis_old, completePointTwoCanonicalBasis_old]

/-- The middle order-three vector is the included original order-two lift. -/
theorem completePointThreeCanonicalBasis_x (i : Fin n) :
    completePointThreeCanonicalBasis K n h i (Sum.inl (Sum.inr ())) =
      divisorPowerRingStep (exactVeroneseProjToBase K n h).appTop.hom
        (completeBaseMarking_relativeCartier K n h i).1 2 (completePointPoleLift K n h i 0) := by
  rw [completePointThreeCanonicalBasis_old, completePointTwoCanonicalBasis_new]

end FLT.Mazur.PolygonInfinitesimalStages
