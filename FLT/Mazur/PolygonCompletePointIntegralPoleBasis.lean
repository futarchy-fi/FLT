/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointSectionRank
public import FLT.Mazur.PolygonCompletePointPoleFrame

/-!
# Integral bases compatible with the original positive pole filtration

The finite rank calculation supplies the initial degree-one basis. The original
pole splitting extends it to degrees two and three, preserving the actual
inclusions and normalized leading terms. The initial basis has not yet been
identified with the canonical divisor section; these are filtration bases,
not a claim of monomial coordinates or of a relative cubic construction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Module

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve FCurve.ModuleLineBundleTensorPullback IncreasingCechCoefficients

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- A finite integral H0 basis of every positive original point power. -/
def completePointPowerHZeroBasis (i : Fin n) (m : ℕ) :
    Basis (Fin (m + 1)) Γ(Spec (.of (PowerSeries K)), ⊤)
      (ModuleRingH (exactVeroneseProjToBase K n h).appTop.hom
        (tensorPower (completePointLine K n h i) (m + 1)) 0) :=
  (completePointPowerSectionsBasis K n h i m).map
    (ringHZeroBaseSections _ (exactVeroneseProjToBase K n h).appTop.hom).symm

/-- The original degree-two pole module has an integral adapted basis. -/
def completePointTwoIntegralBasis (i : Fin n) :
    Basis (Fin 1 ⊕ Unit) Γ(Spec (.of (PowerSeries K)), ⊤)
      (ModuleRingH (exactVeroneseProjToBase K n h).appTop.hom
        (tensorPower (completePointLine K n h i) 2) 0) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : Subsingleton (ModuleH (tensorPower
      (divisorLineBundle (completeBaseMarking K n h i).ker
        (completeBaseMarking_relativeCartier K n h i).1) (0 + 1)) 1) :=
    completePointPower_positive K n h i 0 0
  exact sectionPoleNormalizedBasis (exactVeroneseProjToBase K n h)
    (completeBaseMarking K n h i) (completeBaseMarking_toBase K n h i)
    (completeBaseMarking_relativeCartier K n h i).1 1
    (completePointPowerHZeroBasis K n h i 0) (completePointPoleFrame K n h i 2)

/-- The original degree-three pole module extends the degree-two adapted basis. -/
def completePointThreeIntegralBasis (i : Fin n) :
    Basis ((Fin 1 ⊕ Unit) ⊕ Unit) Γ(Spec (.of (PowerSeries K)), ⊤)
      (ModuleRingH (exactVeroneseProjToBase K n h).appTop.hom
        (tensorPower (completePointLine K n h i) 3) 0) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : Subsingleton (ModuleH (tensorPower
      (divisorLineBundle (completeBaseMarking K n h i).ker
        (completeBaseMarking_relativeCartier K n h i).1) (1 + 1)) 1) :=
    completePointPower_positive K n h i 1 0
  exact sectionPoleNormalizedBasis (exactVeroneseProjToBase K n h)
    (completeBaseMarking K n h i) (completeBaseMarking_toBase K n h i)
    (completeBaseMarking_relativeCartier K n h i).1 2
    (completePointTwoIntegralBasis K n h i) (completePointPoleFrame K n h i 3)

/-- The degree-one vector is retained by the actual divisor transition. -/
theorem completePointTwoIntegralBasis_old (i : Fin n) (j : Fin 1) :
    completePointTwoIntegralBasis K n h i (Sum.inl j) =
      divisorPowerRingStep (exactVeroneseProjToBase K n h).appTop.hom
        (completeBaseMarking_relativeCartier K n h i).1 1
        (completePointPowerHZeroBasis K n h i 0 j) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : Subsingleton (ModuleH (tensorPower
      (divisorLineBundle (completeBaseMarking K n h i).ker
        (completeBaseMarking_relativeCartier K n h i).1) (0 + 1)) 1) :=
    completePointPower_positive K n h i 0 0
  exact sectionPoleAdaptedBasis_old (exactVeroneseProjToBase K n h)
    (completeBaseMarking K n h i) (completeBaseMarking_toBase K n h i)
    (completeBaseMarking_relativeCartier K n h i).1 1 _ _ j

/-- The added degree-two vector is the normalized integral pole lift. -/
theorem completePointTwoIntegralBasis_new (i : Fin n) :
    completePointTwoIntegralBasis K n h i (Sum.inr ()) = completePointPoleLift K n h i 0 := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : Subsingleton (ModuleH (tensorPower
      (divisorLineBundle (completeBaseMarking K n h i).ker
        (completeBaseMarking_relativeCartier K n h i).1) (0 + 1)) 1) :=
    completePointPower_positive K n h i 0 0
  exact sectionPoleNormalizedBasis_new (exactVeroneseProjToBase K n h)
    (completeBaseMarking K n h i) (completeBaseMarking_toBase K n h i)
    (completeBaseMarking_relativeCartier K n h i).1 1 _ _

/-- Both old degree-two vectors enter degree three through the original inclusion. -/
theorem completePointThreeIntegralBasis_old (i : Fin n) (j : Fin 1 ⊕ Unit) :
    completePointThreeIntegralBasis K n h i (Sum.inl j) =
      divisorPowerRingStep (exactVeroneseProjToBase K n h).appTop.hom
        (completeBaseMarking_relativeCartier K n h i).1 2
        (completePointTwoIntegralBasis K n h i j) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : Subsingleton (ModuleH (tensorPower
      (divisorLineBundle (completeBaseMarking K n h i).ker
        (completeBaseMarking_relativeCartier K n h i).1) (1 + 1)) 1) :=
    completePointPower_positive K n h i 1 0
  exact sectionPoleAdaptedBasis_old (exactVeroneseProjToBase K n h)
    (completeBaseMarking K n h i) (completeBaseMarking_toBase K n h i)
    (completeBaseMarking_relativeCartier K n h i).1 2 _ _ j

/-- The final degree-three vector is the normalized integral pole lift. -/
theorem completePointThreeIntegralBasis_new (i : Fin n) :
    completePointThreeIntegralBasis K n h i (Sum.inr ()) = completePointPoleLift K n h i 1 := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : Subsingleton (ModuleH (tensorPower
      (divisorLineBundle (completeBaseMarking K n h i).ker
        (completeBaseMarking_relativeCartier K n h i).1) (1 + 1)) 1) :=
    completePointPower_positive K n h i 1 0
  exact sectionPoleNormalizedBasis_new (exactVeroneseProjToBase K n h)
    (completeBaseMarking K n h i) (completeBaseMarking_toBase K n h i)
    (completeBaseMarking_relativeCartier K n h i).1 2 _ _

end FLT.Mazur.PolygonInfinitesimalStages
