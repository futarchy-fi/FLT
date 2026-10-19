/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGenericClosureSmoothPart
public import FLT.Mazur.WeierstrassGenericClosureZero
public import FLT.Mazur.WeierstrassSmoothNegation

/-!
# Zero and inverse on the retained closure's smooth intersection

The original zero lies in the smooth intersection, and the original inverse
restricts to it. Both projection equations retain the full closure and smooth model.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  (W : WeierstrassCurve R) {H : Scheme}
  (i : H ⟶ integralCurve (W.map (algebraMap R K)))

section Negation

variable [IsClosedImmersion i] (n : H ⟶ H)
  (hn : n ≫ i = i ≫ integralCurveNegation (W.map (algebraMap R K)))

/-- Restrict the extended inverse to the same closure's smooth intersection. -/
def genericClosureSmoothNegation : genericClosureSmoothPart W i ⟶ genericClosureSmoothPart W i :=
  pullback.lift (genericClosureSmoothToClosure W i ≫ genericClosureNegation W i n hn)
    (genericClosureSmoothInclusion W i ≫ integralSmoothNegation W) (by
      simp only [Category.assoc, genericClosureNegation_inclusion, integralSmoothNegation_inclusion]
      rw [← Category.assoc, (genericClosureSmooth_isPullback W i).w, Category.assoc])

/-- The restricted inverse retains the extended inverse on the original closure. -/
@[reassoc] theorem genericClosureSmoothNegation_toClosure :
    genericClosureSmoothNegation W i n hn ≫ genericClosureSmoothToClosure W i =
      genericClosureSmoothToClosure W i ≫ genericClosureNegation W i n hn :=
  pullback.lift_fst _ _ _

/-- The restricted inverse is precisely the actual smooth group's inverse. -/
@[reassoc] theorem genericClosureSmoothNegation_inclusion :
    genericClosureSmoothNegation W i n hn ≫ genericClosureSmoothInclusion W i =
      genericClosureSmoothInclusion W i ≫ integralSmoothNegation W := pullback.lift_snd _ _ _

/-- The inverse on the actual smooth intersection is involutive. -/
@[reassoc] theorem genericClosureSmoothNegation_comp :
    genericClosureSmoothNegation W i n hn ≫ genericClosureSmoothNegation W i n hn = 𝟙 _ := by
  apply (cancel_mono (genericClosureSmoothInclusion W i)).mp
  simp only [Category.assoc, genericClosureSmoothNegation_inclusion,
    genericClosureSmoothNegation_inclusion_assoc, integralSmoothNegation_comp,
    Category.comp_id, Category.id_comp]

end Negation

variable [IsFractionRing R K]
  (z : Spec (.of K) ⟶ H) (hz : z ≫ i = integralCurveZero (W.map (algebraMap R K)))

/-- The extended zero lies in the actual smooth intersection. -/
def genericClosureSmoothZero : Spec (.of R) ⟶ genericClosureSmoothPart W i :=
  pullback.lift (genericClosureZero W i z hz) (integralSmoothZero W) (by
    rw [genericClosureZero_inclusion, integralSmoothZero_inclusion])

/-- The smooth identity retains the original closure's identity. -/
@[reassoc] theorem genericClosureSmoothZero_toClosure :
    genericClosureSmoothZero W i z hz ≫ genericClosureSmoothToClosure W i =
      genericClosureZero W i z hz := pullback.lift_fst _ _ _

/-- The smooth identity is precisely the actual ambient smooth identity. -/
@[reassoc] theorem genericClosureSmoothZero_inclusion :
    genericClosureSmoothZero W i z hz ≫ genericClosureSmoothInclusion W i = integralSmoothZero W :=
  pullback.lift_snd _ _ _

/-- The smooth identity is a section over the original integral base. -/
@[reassoc] theorem genericClosureSmoothZero_structure :
    genericClosureSmoothZero W i z hz ≫ genericClosureSmoothStructure W i = 𝟙 _ := by
  rw [genericClosureSmoothStructure, genericClosureSmoothZero_toClosure_assoc,
    genericClosureZero_structure]

end FLT.Mazur.WeierstrassIntegralChart
