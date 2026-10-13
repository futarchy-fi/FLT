/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointCanonicalPoleBasis

/-!
# Integral monomial bases through degree six

The actual square, mixed product and cube extend the canonically normalized
low-pole basis. Every old vector retains the original divisor inclusion.
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

/-- The actual square extends the integral basis through degree 4. -/
def completePointFourMonomialBasis (i : Fin n) :
    Basis (((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) Γ(Spec (.of (PowerSeries K)), ⊤)
      (ModuleRingH (exactVeroneseProjToBase K n h).appTop.hom
        (tensorPower (completePointLine K n h i) 4) 0) :=
  completePointSpecifiedBasis K n h i 3 (completePointThreeCanonicalBasis K n h i)
    (completePointPoleSquare K n h i) (completePointPoleSquare_coefficient K n h i)

/-- The added degree-4 vector is the original square. -/
theorem completePointFourMonomialBasis_new (i : Fin n) :
    completePointFourMonomialBasis K n h i (Sum.inr ()) = completePointPoleSquare K n h i :=
  completePointSpecifiedBasis_new _ _ _ _ _ _ _ _

/-- The degree-4 basis preserves the original inclusion of the preceding basis. -/
theorem completePointFourMonomialBasis_old (i : Fin n) (j : ((Unit ⊕ Unit) ⊕ Unit)) :
    completePointFourMonomialBasis K n h i (Sum.inl j) =
      divisorPowerRingStep (exactVeroneseProjToBase K n h).appTop.hom
        (completeBaseMarking_relativeCartier K n h i).1 3
        (completePointThreeCanonicalBasis K n h i j) :=
  completePointSpecifiedBasis_old _ _ _ _ _ _ _ _ j

/-- The actual mixed extends the integral basis through degree 5. -/
def completePointFiveMonomialBasis (i : Fin n) :
    Basis ((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) Γ(Spec (.of (PowerSeries K)), ⊤)
      (ModuleRingH (exactVeroneseProjToBase K n h).appTop.hom
        (tensorPower (completePointLine K n h i) 5) 0) :=
  completePointSpecifiedBasis K n h i 4 (completePointFourMonomialBasis K n h i)
    (completePointPoleMixed K n h i) (completePointPoleMixed_coefficient K n h i)

/-- The added degree-5 vector is the original mixed. -/
theorem completePointFiveMonomialBasis_new (i : Fin n) :
    completePointFiveMonomialBasis K n h i (Sum.inr ()) = completePointPoleMixed K n h i :=
  completePointSpecifiedBasis_new _ _ _ _ _ _ _ _

/-- The degree-5 basis preserves the original inclusion of the preceding basis. -/
theorem completePointFiveMonomialBasis_old (i : Fin n) (j : (((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit)) :
    completePointFiveMonomialBasis K n h i (Sum.inl j) =
      divisorPowerRingStep (exactVeroneseProjToBase K n h).appTop.hom
        (completeBaseMarking_relativeCartier K n h i).1 4
        (completePointFourMonomialBasis K n h i j) :=
  completePointSpecifiedBasis_old _ _ _ _ _ _ _ _ j

/-- The actual cube extends the integral basis through degree 6. -/
def completePointSixMonomialBasis (i : Fin n) :
    Basis (((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit) Γ(Spec (.of (PowerSeries K)), ⊤)
      (ModuleRingH (exactVeroneseProjToBase K n h).appTop.hom
        (tensorPower (completePointLine K n h i) 6) 0) :=
  completePointSpecifiedBasis K n h i 5 (completePointFiveMonomialBasis K n h i)
    (completePointPoleCube K n h i) (completePointPoleCube_coefficient K n h i)

/-- The added degree-6 vector is the original cube. -/
theorem completePointSixMonomialBasis_new (i : Fin n) :
    completePointSixMonomialBasis K n h i (Sum.inr ()) = completePointPoleCube K n h i :=
  completePointSpecifiedBasis_new _ _ _ _ _ _ _ _

/-- The degree-6 basis preserves the original inclusion of the preceding basis. -/
theorem completePointSixMonomialBasis_old (i : Fin n)
    (j : ((((Unit ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit)) :
    completePointSixMonomialBasis K n h i (Sum.inl j) =
      divisorPowerRingStep (exactVeroneseProjToBase K n h).appTop.hom
        (completeBaseMarking_relativeCartier K n h i).1 5
        (completePointFiveMonomialBasis K n h i j) :=
  completePointSpecifiedBasis_old _ _ _ _ _ _ _ _ j

/-- In degree six the cube coordinate is exactly the original leading coefficient. -/
theorem completePointSixMonomialBasis_repr_last (i : Fin n)
    (z : ModuleRingH (exactVeroneseProjToBase K n h).appTop.hom
      (tensorPower (completePointLine K n h i) 6) 0) :
    (completePointSixMonomialBasis K n h i).repr z (Sum.inr ()) =
      completePointPoleCoefficient K n h i 6 z :=
  completePointSpecifiedBasis_repr_last _ _ _ _ _ _ _ _ z

/-- The order-three square has cube coefficient exactly one over the complete base. -/
theorem completePointSixMonomialBasis_YSquare_last (i : Fin n) :
    (completePointSixMonomialBasis K n h i).repr
      (completePointPoleYSquare K n h i) (Sum.inr ()) = 1 := by
  rw [completePointSixMonomialBasis_repr_last, completePointPoleYSquare_coefficient]

end FLT.Mazur.PolygonInfinitesimalStages
