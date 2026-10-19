/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGenericClosureSmoothPart
public import FLT.Mazur.WeierstrassSmoothCoefficientCartesian

/-!
# The original generic kernel is dense in the closure's smooth intersection

A smooth generic cubic maps into the integral relative smooth open. The exact
original kernel therefore factors through the smooth intersection, and flat
base change proves its schematic density there.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassDividedDepth

set_option backward.isDefEq.respectTransparency false

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  (W : WeierstrassCurve R) (hΔ : IsUnit (W.map (algebraMap R K)).Δ)

/-- The full smooth generic cubic maps into the actual integral smooth open. -/
def genericCurveToIntegralSmooth :
    integralCurve (W.map (algebraMap R K)) ⟶ (integralSmoothOpen W).toScheme :=
  IsOpenImmersion.lift (integralSmoothOpen W).ι (integralCoefficientMorphism W) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change x ∈ (integralCoefficientMorphism W ⁻¹ᵁ integralSmoothOpen W)
    rw [integralCoefficientMorphism_preimage_smooth]
    let _ := integralCurveStructure_smooth (W.map (algebraMap R K)) hΔ
    rw [integralSmoothOpen, Scheme.Hom.smoothLocus_eq_top]
    trivial)

/-- The smooth factorization retains the actual coefficient map on the whole generic cubic. -/
@[reassoc] theorem genericCurveToIntegralSmooth_inclusion :
    genericCurveToIntegralSmooth W hΔ ≫ (integralSmoothOpen W).ι =
      integralCoefficientMorphism W := IsOpenImmersion.lift_fac _ _ _

variable {H : Scheme} (i : H ⟶ integralCurve (W.map (algebraMap R K)))

/-- Retain the original generic kernel in the same closure's smooth intersection. -/
def genericKernelToClosureSmooth : H ⟶ genericClosureSmoothPart W i :=
  pullback.lift (genericKernelToClosure W i) (i ≫ genericCurveToIntegralSmooth W hΔ) (by
    rw [Category.assoc, genericCurveToIntegralSmooth_inclusion,
      genericKernelToClosure_inclusion])

/-- The generic smooth factorization retains the exact original map to the full closure. -/
@[reassoc] theorem genericKernelToClosureSmooth_toClosure :
    genericKernelToClosureSmooth W hΔ i ≫ genericClosureSmoothToClosure W i =
      genericKernelToClosure W i := pullback.lift_fst _ _ _

/-- The generic smooth factorization retains the original embedded generic kernel. -/
@[reassoc] theorem genericKernelToClosureSmooth_inclusion :
    genericKernelToClosureSmooth W hΔ i ≫ genericClosureSmoothInclusion W i =
      i ≫ genericCurveToIntegralSmooth W hΔ := pullback.lift_snd _ _ _

/-- The same generic source is the pullback along the closure's open intersection. -/
theorem genericKernelToClosureSmooth_isPullback :
    IsPullback (𝟙 H) (genericKernelToClosureSmooth W hΔ i)
      (genericKernelToClosure W i) (genericClosureSmoothToClosure W i) :=
  IsPullback.of_horiz_isIso_mono
    ⟨by rw [Category.id_comp, genericKernelToClosureSmooth_toClosure]⟩

variable [IsClosedImmersion i]

/-- Schematic density of the exact original kernel survives the open intersection. -/
instance genericKernelToClosureSmooth_dense :
    IsSchemeTheoreticallyDominant (genericKernelToClosureSmooth W hΔ i) :=
  IsSchemeTheoreticallyDominant.of_isPullback (genericKernelToClosureSmooth_isPullback W hΔ i)

/-- The original generic source is quasi-compact in the actual smooth intersection. -/
instance genericKernelToClosureSmooth_quasiCompact :
    QuasiCompact (genericKernelToClosureSmooth W hΔ i) :=
  MorphismProperty.of_isPullback (genericKernelToClosureSmooth_isPullback W hΔ i)
    (inferInstanceAs (QuasiCompact (genericKernelToClosure W i)))

end FLT.Mazur.WeierstrassIntegralChart
