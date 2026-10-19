/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGenericClosureSmoothPart
public import FLT.Mazur.WeierstrassSmoothGoodReductionGroup
public import FLT.Mazur.WeierstrassValuationKernelClosureDegree

/-!
# Retaining the full finite kernel in good reduction

When the original integral cubic has unit discriminant, its smooth intersection
is the entire original closure. The actual projection is an isomorphism over the
original base, so the full finite locally free degree transfers without replacing
the embedded kernel. This result makes no claim at bad reduction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  (W : WeierstrassCurve R) {H : Scheme}
  (i : H ⟶ integralCurve (W.map (algebraMap R K))) (hΔ : IsUnit W.Δ)

include hΔ in
/-- In good reduction, the original smooth intersection is the entire original closure. -/
theorem genericClosureSmoothToClosure_isIso : IsIso (genericClosureSmoothToClosure W i) := by
  let _ := integralSmoothOverInclusion_isIso W hΔ
  let _ : IsIso (integralSmoothOpen W).ι :=
    inferInstanceAs (IsIso ((Over.forget (Spec (.of R))).map (integralSmoothOverInclusion W)))
  exact inferInstanceAs (IsIso (Limits.pullback.fst _ _))

/-- The exact original projection identifies the smooth intersection with the full closure. -/
def genericClosureSmoothFullIso : genericClosureSmoothPart W i ≅ genericKernelClosure W i := by
  let _ := genericClosureSmoothToClosure_isIso W i hΔ
  exact asIso (genericClosureSmoothToClosure W i)

/-- The full-closure comparison retains the original coefficient morphism. -/
def genericClosureSmoothFullOverIso :
    Over.mk (genericClosureSmoothStructure W i) ≅ Over.mk (genericKernelClosureStructure W i) :=
  Over.isoMk (genericClosureSmoothFullIso W i hΔ) rfl

/-- The original smooth inclusion still factors through the same full closed embedding. -/
@[reassoc] theorem genericClosureSmoothFullIso_inclusion :
    (genericClosureSmoothFullIso W i hΔ).hom ≫ genericKernelClosureInclusion W i =
      genericClosureSmoothInclusion W i ≫ (integralSmoothOpen W).ι :=
  (genericClosureSmooth_isPullback W i).w

variable [IsDomain R] [ValuationRing R] [IsNoetherianRing R] [IsFractionRing R K]
  [IsClosedImmersion i]

include hΔ in
/-- Good reduction transports the full original finite locally free degree to the smooth kernel. -/
theorem genericClosureSmoothStructure_degree_goodReduction (n : ℕ)
    (hd : FCurve.FiniteLocallyFreeDegree
      (i ≫ integralCurveStructure (W.map (algebraMap R K))) n) :
    FCurve.FiniteLocallyFreeDegree (genericClosureSmoothStructure W i) n :=
  (FCurve.finiteLocallyFreeDegree_iff_of_overIso
    (genericClosureSmoothFullOverIso W i hΔ)).mpr (genericKernelClosureStructure_degree W i n hd)

end FLT.Mazur.WeierstrassIntegralChart
