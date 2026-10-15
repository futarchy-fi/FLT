/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticVeroneseGrading
public import FLT.Mazur.PolygonArithmeticZeroCoefficients

/-!
# Complete coefficients as the internal degree-zero ring

The canonical scalar map of the internally graded compatible Veronese
algebra is bijective in degree zero. This identifies the actual Proj base
ring with the original integral coefficient ring.
-/

@[expose] public noncomputable section

open scoped DirectSum

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A : Type) [CommRing A] (π : A) (n : ℕ) (h : 2 ≤ n) (q : ℕ)

/-- Original complete coefficients are inserted into the retained degree zero. -/
theorem compatibleVeronese_algebraMap_zero (r : A) :
    algebraMap A (CompatibleVeroneseSections A π n h q) r =
      DirectSum.of _ 0 (show compatibleVeroneseDegree A π n h q 0 from
        compatibleZeroScalars A π n h r) := by
  rw [DirectSum.algebraMap_apply]
  congr 1
  apply Subtype.ext
  change algebraMap A (CompatibleSections A π n h) r = r • 1
  simp only [Algebra.smul_def, mul_one]

variable [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] [NeZero n]

include hne hgen in
/-- The actual degree-zero structural scalar map is bijective. -/
theorem compatibleVeronese_zero_algebraMap_bijective : Function.Bijective
    (algebraMap A (compatibleVeroneseGrade A π n h q 0)) := by
  constructor
  · intro r s he
    have hv := congrArg Subtype.val he
    change algebraMap A (CompatibleVeroneseSections A π n h q) r =
      algebraMap A (CompatibleVeroneseSections A π n h q) s at hv
    rw [compatibleVeronese_algebraMap_zero, compatibleVeronese_algebraMap_zero] at hv
    exact compatibleZeroScalars_injective A π n h (DirectSum.of_injective 0 hv)
  · rintro ⟨_, ⟨s, rfl⟩⟩
    obtain ⟨r, hr⟩ := compatibleZeroScalars_surjective A π n h hne hgen
      (show compatibleSectionDegree A π n h 0 from s)
    refine ⟨r, Subtype.ext ?_⟩
    change algebraMap A (CompatibleVeroneseSections A π n h q) r =
      DirectSum.of _ 0 s
    rw [compatibleVeronese_algebraMap_zero]
    exact congrArg (DirectSum.of (fun d ↦ ↥(compatibleVeroneseDegree A π n h q d)) 0) hr

/-- The degree-zero ring comparison is the original structural scalar map. -/
def compatibleVeroneseZeroRingEquiv :
    A ≃+* compatibleVeroneseGrade A π n h q 0 :=
  RingEquiv.ofBijective _ (compatibleVeronese_zero_algebraMap_bijective A π n h q hne hgen)

end FLT.Mazur.PolygonArithmeticStages
