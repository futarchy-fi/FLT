/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupFractionChartMap
public import FLT.Mazur.BlowupReesRatioTransition

/-!
# Fraction lifts on the actual input ratio opens

An ideal-preserving map lifts from an output fraction chart to the open of an
input chart where the ratio of its image denominator is invertible. Only the
ratio is inverted. The original input denominator remains regular there.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.BlowupFractionChart

open BlowupRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 2048

variable {A B : Type*} [CommRing A] [CommRing B]
  (I : Ideal A) (J : Ideal B) (φ : A →+* B) (hφ : I.map φ ≤ J)
  (f : B) (hf : f ∈ J) (a : A) (ha : a ∈ I)

/-- The target fraction chart maps into the full input ratio open. -/
irreducible_def ratioLift : chart I a →+*
    FractionRatioOpen J f (φ a) (hφ (Ideal.mem_map_of_mem φ ha)) :=
  ((ratioTransition J (φ a) (hφ (Ideal.mem_map_of_mem φ ha)) f hf).toRingHom.comp
    (algebraMap (chart J (φ a)) _)).comp (chartMap I J φ hφ a)

/-- The ratio-open lift retains exactly the original coefficient homomorphism. -/
@[simp] theorem ratioLift_base (z : A) :
    ratioLift I J φ hφ f hf a ha (algebraMap A _ z) =
      originalOnRatio J f (φ a) (hφ (Ideal.mem_map_of_mem φ ha)) (φ z) := by
  rw [ratioLift_def, RingHom.comp_apply, RingHom.comp_apply, chartMap_base]
  change ratioTransition J (φ a) _ f hf (originalOnRatio J (φ a) f hf (φ z)) = _
  exact ratioTransition_original J (φ a) _ f hf (φ z)

/-- Each image ratio satisfies the original numerator equation on the entire input open. -/
theorem ratioLift_ratio_equation (z : A) (hz : z ∈ I) :
    originalOnRatio J f (φ a) (hφ (Ideal.mem_map_of_mem φ ha)) (φ a) *
        ratioLift I J φ hφ f hf a ha (ratio I a z hz) =
      originalOnRatio J f (φ a) (hφ (Ideal.mem_map_of_mem φ ha)) (φ z) := by
  rw [← ratioLift_base I J φ hφ f hf a ha a, ← map_mul]
  rw [show algebraMap A (chart I a) a = denominator I a from rfl]
  rw [denominator_mul_ratio, ratioLift_base]

/-- The output denominator is regular on the constructed input ratio open. -/
theorem ratioLift_denominator_regular :
    IsRegular (ratioLift I J φ hφ f hf a ha (denominator I a)) := by
  rw [denominator, ratioLift_base]
  exact originalOnRatio_numerator_regular J f (φ a) _

/-- Original coefficients uniquely characterize the lift, also along exceptional points. -/
theorem ratioLift_unique
    (k : chart I a →+* FractionRatioOpen J f (φ a) (hφ (Ideal.mem_map_of_mem φ ha)))
    (hk : ∀ z, k (algebraMap A _ z) =
      originalOnRatio J f (φ a) (hφ (Ideal.mem_map_of_mem φ ha)) (φ z)) :
    k = ratioLift I J φ hφ f hf a ha := by
  have he : (ratioLift I J φ hφ f hf a ha).comp (algebraMap A _) =
      k.comp (algebraMap A _) := by
    ext z
    exact (ratioLift_base I J φ hφ f hf a ha z).trans (hk z).symm
  exact (ringHom_ext_of_denominator_regular I a
    (S := FractionRatioOpen J f (φ a) (hφ (Ideal.mem_map_of_mem φ ha)))
    (ratioLift I J φ hφ f hf a ha) k he
    (ratioLift_denominator_regular I J φ hφ f hf a ha)).symm

end FLT.Mazur.BlowupFractionChart
