/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientHilbertUniversalPullback

/-!
# Full families of arbitrary parameters on actual Hilbert overlaps

The universal pair compatibility pulls back along every test-scheme map to
an overlap. Thus the two containing-chart parameters classify equal full
families in the original ambient.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover

universe u

namespace FLT.Mazur.HilbertChart.AmbientQuotientCharts

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {z : Z ⟶ Spec (.of R)}
variable (A : AmbientQuotientCharts R z) (d : ℕ) [IsSeparated z]
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R)) (i j : A.Index)
variable (p : X ⟶ (A.overlap d i j).toScheme) (hp : p ≫ A.overlapBase d i j = s)

/-- Every actual overlap parameter gives equal full families in its two containing charts. -/
theorem chartParameterFamily_overlap :
    A.chartParameterFamily d s j
        ⟨p ≫ (A.transition d i j).hom ≫ (A.overlap d j i).ι, by
          rw [Category.assoc, Category.assoc, A.transition_over]
          exact hp⟩ =
      A.chartParameterFamily d s i
        ⟨p ≫ (A.overlap d i j).ι, (Category.assoc _ _ _).trans hp⟩ := by
  have h := congrArg
    (relativeIdealFamilyBaseChange z d (A.overlapBase d i j) s p hp)
    (A.chartUniversalFamily_pair d i j)
  rw [relativeIdealFamilyBaseChange_comp, relativeIdealFamilyBaseChange_comp] at h
  rw [← A.chartUniversalFamily_pullback, ← A.chartUniversalFamily_pullback]
  exact h

end FLT.Mazur.HilbertChart.AmbientQuotientCharts
