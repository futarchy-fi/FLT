/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGenericKernelClosure
public import FLT.Mazur.WeierstrassRelativeSmoothOpen

/-!
# The smooth part of the same integral kernel closure

Intersect the actual closed kernel model with the relative smooth open. This is
an open part of the original closure, not an assertion that all of it is smooth.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  (W : WeierstrassCurve R) {H : Scheme}
  (i : H ⟶ integralCurve (W.map (algebraMap R K)))

/-- Intersect the retained closure with the original relative smooth open. -/
def genericClosureSmoothPart : Scheme :=
  pullback (genericKernelClosureInclusion W i) (integralSmoothOpen W).ι

/-- The smooth intersection's original open embedding into the full closure. -/
def genericClosureSmoothToClosure : genericClosureSmoothPart W i ⟶ genericKernelClosure W i :=
  pullback.fst _ _

/-- The same intersection is closed in the actual smooth group scheme. -/
def genericClosureSmoothInclusion :
    genericClosureSmoothPart W i ⟶ (integralSmoothOpen W).toScheme := pullback.snd _ _

/-- The smooth intersection retains both original embeddings, as a Cartesian square. -/
theorem genericClosureSmooth_isPullback :
    IsPullback (genericClosureSmoothToClosure W i) (genericClosureSmoothInclusion W i)
      (genericKernelClosureInclusion W i) (integralSmoothOpen W).ι :=
  IsPullback.of_hasPullback _ _

/-- The intersection is open in the actual closure, with no avoidance assumption. -/
instance genericClosureSmoothToClosure_open : IsOpenImmersion (genericClosureSmoothToClosure W i) :=
  inferInstanceAs (IsOpenImmersion (pullback.fst _ _))

/-- The intersection is closed in the actual smooth ambient model. -/
instance genericClosureSmoothInclusion_closed :
    IsClosedImmersion (genericClosureSmoothInclusion W i) :=
  inferInstanceAs (IsClosedImmersion (pullback.snd _ _))

/-- The inherited coefficient structure of the same smooth intersection. -/
def genericClosureSmoothStructure : genericClosureSmoothPart W i ⟶ Spec (.of R) :=
  genericClosureSmoothToClosure W i ≫ genericKernelClosureStructure W i

/-- Its structure is equally computed through the actual smooth ambient group. -/
@[reassoc] theorem genericClosureSmoothInclusion_structure :
    genericClosureSmoothInclusion W i ≫ integralSmoothStructure W =
      genericClosureSmoothStructure W i := by
  rw [integralSmoothStructure, ← Category.assoc,
    ← (genericClosureSmooth_isPullback W i).w, Category.assoc]
  rfl

/-- Flatness of the constructed full closure passes to its actual smooth part. -/
instance genericClosureSmoothStructure_flat [Flat (genericKernelClosureStructure W i)] :
    Flat (genericClosureSmoothStructure W i) :=
  inferInstanceAs (Flat (genericClosureSmoothToClosure W i ≫ genericKernelClosureStructure W i))

end FLT.Mazur.WeierstrassIntegralChart
