/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointNewSections
public import FLT.Mazur.DivisorPowerLeadingClass

/-!
# Actual nonzero leading classes for the original point powers

Every positive pole step on every original field square surjects onto its
actual divisor quotient. The previously chosen new sections have nonzero
classes there; no choice of a Weierstrass equation is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] {Y : Scheme}
  (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

/-- The original field-square leading map attains every quotient class in positive steps. -/
theorem completeCartesianPointLeadingClass_surjective (i : Fin n) (m : ℕ) (hm : 0 < m) :
    Function.Surjective (divisorPowerLeadingClass q
      (completeCartesianMarking_relativeCartier K n h s p q hs i).1 m) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  let _ : Subsingleton (ModuleScalarH q
      (tensorPower (divisorLineBundle (completeCartesianMarking K n h s p q hs i).ker
        (completeCartesianMarking_relativeCartier K n h s p q hs i).1) (a + 1)) 1) :=
    completeCartesianPointPower_affine_positive K n h s p q hs i a 0
  exact divisorPowerLeadingClass_surjective q _ (a + 1)

/-- The actual new section has nonzero leading class in the original quotient coefficient. -/
theorem completeCartesianPointNewSection_leading_ne_zero
    (i : Fin n) (m : ℕ) (hm : 0 < m) :
    divisorPowerLeadingClass q
      (completeCartesianMarking_relativeCartier K n h s p q hs i).1 m
      ((moduleScalarH0Equiv q _).symm
        (completeCartesianPointNewSection K n h L s p q hs i m hm)) ≠ 0 :=
  (divisorPowerLeadingClass_ne_zero_iff q _ m _).mpr
    (completeCartesianPointNewSection_not_mem_range K n h L s p q hs i m hm)

end FLT.Mazur.PolygonInfinitesimalStages
