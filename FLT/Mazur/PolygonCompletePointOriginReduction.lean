/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointOriginIdeal

/-!
# The reduced inverse image of the cubic origin is the original marking

The complete coefficient ring is reduced, so the original marking ideal is radical.
The proved support comparison therefore identifies the radical of the pulled origin
ideal, without discarding possible multiplicities in the still-open comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "s" => completeBaseMarking K n h i

/-- The original complete-base marking has its full reduced scheme structure. -/
theorem completePointMarkingIdeal_radical : (s).ker.radical = (s).ker := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ := FCurve.isClosedImmersion_section _ _ (completeBaseMarking_toBase K n h i)
  ext1
  funext U
  change ((s).ker.ideal U).radical = (s).ker.ideal U
  rw [Scheme.Hom.ker_apply]
  exact Ideal.radical_eq_iff.mpr (Ideal.isRadical_bot.comap ((s).app U).hom)

/-- The radical of the actual pulled cubic-origin ideal is the original marking ideal. -/
theorem completePointPulledOriginIdeal_radical :
    (completePointPulledOriginIdeal K n h i).radical = (s).ker := by
  rw [← Scheme.IdealSheafData.vanishingIdeal_support,
    completePointPulledOriginIdeal_support, Scheme.IdealSheafData.vanishingIdeal_support,
    completePointMarkingIdeal_radical]

/-- Every equation of the pulled cubic origin vanishes on the original marking. -/
theorem completePointPulledOriginIdeal_le :
    completePointPulledOriginIdeal K n h i ≤ (s).ker := by
  rw [← completePointPulledOriginIdeal_radical]
  exact Scheme.IdealSheafData.le_radical _

end FLT.Mazur.PolygonInfinitesimalStages
