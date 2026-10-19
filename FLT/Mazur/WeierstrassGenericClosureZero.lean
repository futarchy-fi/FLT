/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGenericClosureNegation
public import FLT.Mazur.SurjectiveDominantEpi
public import FLT.Mazur.WeierstrassSmoothZeroSection

/-!
# The original zero section lies in the actual integral kernel closure

The fraction-field spectrum detects equations on the base. Thus the generic
kernel's zero constructs a section of its integral closure, without good reduction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] (W : WeierstrassCurve R) {H : Scheme}
  (i : H ⟶ integralCurve (W.map (algebraMap R K))) [IsClosedImmersion i]
  (z : Spec (.of K) ⟶ H) (hz : z ≫ i = integralCurveZero (W.map (algebraMap R K)))

/-- The original zero section factors through the same schematic closure. -/
def genericClosureZero : Spec (.of R) ⟶ genericKernelClosure W i := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let _ : IsSchemeTheoreticallyDominant b :=
    SurjectiveDominantEpi.spec_schematic _ (IsFractionRing.injective R K)
  exact DenseClosedRestriction.lift b (genericKernelClosureInclusion W i)
    (integralCurveZero W) (z ≫ genericKernelToClosure W i) (by
      rw [Category.assoc, genericKernelToClosure_inclusion, ← Category.assoc, hz]
      exact (integralCoefficientMorphism_zero W).symm)

omit [IsClosedImmersion i] in
/-- The constructed section is exactly the original integral zero in the cubic. -/
@[reassoc] theorem genericClosureZero_inclusion :
    genericClosureZero W i z hz ≫ genericKernelClosureInclusion W i = integralCurveZero W := by
  let _ := SurjectiveDominantEpi.spec_schematic _ (IsFractionRing.injective R K)
  unfold genericClosureZero
  exact DenseClosedRestriction.lift_inclusion _ _ _ _ _

omit [IsClosedImmersion i] in
/-- Generic restriction recovers the original generic kernel's zero. -/
@[reassoc] theorem genericClosureZero_generic :
    Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ genericClosureZero W i z hz =
      z ≫ genericKernelToClosure W i := by
  apply (cancel_mono (genericKernelClosureInclusion W i)).mp
  rw [Category.assoc, genericClosureZero_inclusion, Category.assoc,
    genericKernelToClosure_inclusion, ← Category.assoc z, hz]
  exact (integralCoefficientMorphism_zero W).symm

omit [IsClosedImmersion i] in
/-- The constructed zero is a section over the original coefficient spectrum. -/
@[reassoc] theorem genericClosureZero_structure :
    genericClosureZero W i z hz ≫ genericKernelClosureStructure W i = 𝟙 _ := by
  rw [genericKernelClosureStructure, genericClosureZero_inclusion_assoc,
    integralCurveZero_structure]

/-- The extended inverse fixes the constructed integral identity. -/
@[reassoc] theorem genericClosureZero_negation (n : H ⟶ H)
    (hn : n ≫ i = i ≫ integralCurveNegation (W.map (algebraMap R K))) :
    genericClosureZero W i z hz ≫ genericClosureNegation W i n hn =
      genericClosureZero W i z hz := by
  apply (cancel_mono (genericKernelClosureInclusion W i)).mp
  rw [Category.assoc, genericClosureNegation_inclusion, genericClosureZero_inclusion_assoc,
    integralCurveZero_negation, genericClosureZero_inclusion]

end FLT.Mazur.WeierstrassIntegralChart
