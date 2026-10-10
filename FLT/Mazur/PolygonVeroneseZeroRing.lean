/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonVeroneseGrading
public import FLT.Mazur.PolygonCompatibleZeroCoefficients

/-!
# Complete coefficients as the internal degree-zero ring

The canonical scalar map of the internally graded compatible Veronese
algebra is bijective in degree zero. This identifies the actual Proj base
ring with the original power-series coefficient ring.
-/

@[expose] public noncomputable section

open scoped DirectSum

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) (q : ℕ)

/-- Original complete coefficients are inserted into the retained degree zero. -/
theorem compatibleVeronese_algebraMap_zero (r : PowerSeries K) :
    algebraMap (PowerSeries K) (CompatibleVeroneseSections K n h q) r =
      DirectSum.of _ 0 (show compatibleVeroneseDegree K n h q 0 from
        compatibleZeroScalars K n h r) := by
  rw [DirectSum.algebraMap_apply]
  congr 1
  apply Subtype.ext
  change algebraMap (PowerSeries K) (CompatibleSections K n h) r = r • 1
  simp only [Algebra.smul_def, mul_one]

variable [NeZero n]

/-- The actual degree-zero structural scalar map is bijective. -/
theorem compatibleVeronese_zero_algebraMap_bijective : Function.Bijective
    (algebraMap (PowerSeries K) (compatibleVeroneseGrade K n h q 0)) := by
  constructor
  · intro r s he
    have hv := congrArg Subtype.val he
    change algebraMap (PowerSeries K) (CompatibleVeroneseSections K n h q) r =
      algebraMap (PowerSeries K) (CompatibleVeroneseSections K n h q) s at hv
    rw [compatibleVeronese_algebraMap_zero, compatibleVeronese_algebraMap_zero] at hv
    exact compatibleZeroScalars_injective K n h (DirectSum.of_injective 0 hv)
  · rintro ⟨_, ⟨s, rfl⟩⟩
    obtain ⟨r, hr⟩ := compatibleZeroScalars_surjective K n h
      (show compatibleSectionDegree K n h 0 from s)
    refine ⟨r, Subtype.ext ?_⟩
    change algebraMap (PowerSeries K) (CompatibleVeroneseSections K n h q) r =
      DirectSum.of _ 0 s
    rw [compatibleVeronese_algebraMap_zero]
    exact congrArg (DirectSum.of (fun d ↦ ↥(compatibleVeroneseDegree K n h q d)) 0) hr

/-- The degree-zero ring comparison is the original structural scalar map. -/
def compatibleVeroneseZeroRingEquiv :
    PowerSeries K ≃+* compatibleVeroneseGrade K n h q 0 :=
  RingEquiv.ofBijective _ (compatibleVeronese_zero_algebraMap_bijective K n h q)

end FLT.Mazur.PolygonInfinitesimalStages
