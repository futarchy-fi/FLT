/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointPoleProducts
public import FLT.Mazur.SectionPoleSpecifiedBasis

/-!
# Extending complete-base pole bases by actual sections

A section with unit coefficient in the common integral frame extends the
preceding basis through the original divisor inclusion. Its final coordinate
is the actual leading coefficient, with no choice of another pole lift.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Module
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor sectionPoleMultiplicativeCoordinates

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
  {ι : Type} (b : Basis ι Γ(Spec (.of (PowerSeries K)), ⊤)
    (ModuleRingH (exactVeroneseProjToBase K n h).appTop.hom
      (tensorPower (completePointLine K n h i) m) 0))
  (v : ModuleRingH (exactVeroneseProjToBase K n h).appTop.hom
    (tensorPower (completePointLine K n h i) (m + 1)) 0)
  (hv : completePointPoleCoefficient K n h i (m + 1) v = 1)

/-- Extend by the specified integral section with leading coefficient one. -/
def completePointSpecifiedBasis : Basis (ι ⊕ Unit) Γ(Spec (.of (PowerSeries K)), ⊤)
    (ModuleRingH (exactVeroneseProjToBase K n h).appTop.hom
      (tensorPower (completePointLine K n h i) (m + 1)) 0) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  exact sectionPoleSpecifiedBasis (exactVeroneseProjToBase K n h)
    (completeBaseMarking K n h i) (completeBaseMarking_toBase K n h i)
    (completeBaseMarking_relativeCartier K n h i).1 m
    (completePointPoleFrame K n h i (m + 1)) b v
    ((sectionPoleCoefficient_leading (completeBaseMarking K n h i)
      (completeBaseMarking_relativeCartier K n h i).1 (completePointSectionFrame K n h i)
      (exactVeroneseProjToBase K n h) (completeBaseMarking_toBase K n h i) m v).symm.trans hv)

/-- Old vectors enter by the original divisor inclusion. -/
theorem completePointSpecifiedBasis_old (j : ι) :
    completePointSpecifiedBasis K n h i m b v hv (Sum.inl j) =
      divisorPowerRingStep (exactVeroneseProjToBase K n h).appTop.hom
        (completeBaseMarking_relativeCartier K n h i).1 m (b j) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  exact sectionPoleSpecifiedBasis_old _ _ _ _ _ _ _ _ _ j

/-- The added vector is precisely the specified section. -/
theorem completePointSpecifiedBasis_new :
    completePointSpecifiedBasis K n h i m b v hv (Sum.inr ()) = v := by
  let _ := exactVeroneseProjToBase_isProper K n h
  exact sectionPoleSpecifiedBasis_new _ _ _ _ _ _ _ _ _

/-- The final coordinate is the actual common-frame pole coefficient. -/
theorem completePointSpecifiedBasis_repr_last
    (z : ModuleRingH (exactVeroneseProjToBase K n h).appTop.hom
      (tensorPower (completePointLine K n h i) (m + 1)) 0) :
    (completePointSpecifiedBasis K n h i m b v hv).repr z (Sum.inr ()) =
      completePointPoleCoefficient K n h i (m + 1) z := by
  let _ := exactVeroneseProjToBase_isProper K n h
  exact (sectionPoleSpecifiedBasis_repr_new _ _ _ _ _ _ _ _ _ z).trans
    (sectionPoleCoefficient_leading (completeBaseMarking K n h i)
      (completeBaseMarking_relativeCartier K n h i).1 (completePointSectionFrame K n h i)
      (exactVeroneseProjToBase K n h) (completeBaseMarking_toBase K n h i) m z).symm

end FLT.Mazur.PolygonInfinitesimalStages
