/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticIntegralSectionReduction
public import FLT.Mazur.EllipticSubgroupAmbientSectionLaws

/-!
# Smooth integral sections are exactly arithmetic smooth reduction

The section of each E₀ point factors through the actual smooth open.
Conversely any smooth integral section with the prescribed generic point
forces E₀ membership. Separatedness proves uniqueness of the integral extension.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {K : Type u} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- A section with the original generic point is the constructed integral section. -/
theorem integralPointSection_unique
    (P : (W.map (algebraMap A K)).toProjective.Point)
    (s : Spec (.of A) ⟶ integralCurve W) (hs : s ≫ integralCurveStructure W = 𝟙 _)
    (hg : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ s =
      (projectiveToIntegral W P).left) : s = integralPointSection A W P := by
  apply EllipticSubgroupChart.ambientSections_generic_ext A W
  · rw [hs, integralPointSection_structure]
  · rw [hg, integralPointSection_generic]

/-- Every E₀ point extends to the actual relative smooth open over the valuation ring. -/
def smoothIntegralPointSection
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : SmoothReduction A W P) :
    Spec (.of A) ⟶ (integralSmoothOpen W).toScheme :=
  IsOpenImmersion.lift (integralSmoothOpen W).ι (integralPointSection A W P)
    (by rw [Scheme.Opens.range_ι]; exact (integralPointSection_range_smooth_iff A W P).mpr hP)

/-- Its inclusion is the original integral cubic section. -/
@[reassoc] theorem smoothIntegralPointSection_inclusion
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : SmoothReduction A W P) :
    smoothIntegralPointSection A W P hP ≫ (integralSmoothOpen W).ι =
      integralPointSection A W P := IsOpenImmersion.lift_fac _ _ _

/-- The smooth factor is still a section over the original coefficient ring. -/
@[reassoc] theorem smoothIntegralPointSection_structure
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : SmoothReduction A W P) :
    smoothIntegralPointSection A W P hP ≫ integralSmoothStructure W = 𝟙 _ := by
  rw [integralSmoothStructure, ← Category.assoc, smoothIntegralPointSection_inclusion,
    integralPointSection_structure]

/-- The generic restriction retains the exact classical point in the smooth scheme. -/
theorem smoothIntegralPointSection_generic
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : SmoothReduction A W P) :
    Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ smoothIntegralPointSection A W P hP =
      projectiveToSmooth W P := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  rw [Category.assoc, smoothIntegralPointSection_inclusion, projectiveToSmooth_inclusion,
    integralPointSection_generic]

/-- The closed fiber of the smooth section is arithmetic reduction as an actual morphism. -/
theorem smoothIntegralPointSection_special
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : SmoothReduction A W P) :
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫
        smoothIntegralPointSection A W P hP =
      projectiveToSmooth W (smoothReductionPoint A W ⟨P, hP⟩) := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  rw [Category.assoc, smoothIntegralPointSection_inclusion, projectiveToSmooth_inclusion]
  exact integralPointSpecialization_eq_projective A W P hP

/-- Smooth reduction is equivalent to existence of a genuine smooth section of the same point. -/
theorem smoothReduction_iff_exists_smooth_section
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    SmoothReduction A W P ↔
      ∃ s : Spec (.of A) ⟶ (integralSmoothOpen W).toScheme,
        s ≫ integralSmoothStructure W = 𝟙 _ ∧
        Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ s = projectiveToSmooth W P := by
  constructor
  · intro hP
    exact ⟨smoothIntegralPointSection A W P hP,
      smoothIntegralPointSection_structure A W P hP,
      smoothIntegralPointSection_generic A W P hP⟩
  · rintro ⟨s, hs, hg⟩
    have he : s ≫ (integralSmoothOpen W).ι = integralPointSection A W P := by
      apply integralPointSection_unique A W P
      · exact (Category.assoc _ _ _).trans hs
      · rw [← Category.assoc, hg, projectiveToSmooth_inclusion]
    apply (integralPointSection_range_smooth_iff A W P).mp
    rw [← he]
    rintro _ ⟨x, rfl⟩
    exact (s x).property

/-- The actual smooth integral extension of a fixed generic point is unique. -/
theorem smoothIntegralPointSection_unique
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : SmoothReduction A W P)
    (s : Spec (.of A) ⟶ (integralSmoothOpen W).toScheme)
    (hs : s ≫ integralSmoothStructure W = 𝟙 _)
    (hg : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ s = projectiveToSmooth W P) :
    s = smoothIntegralPointSection A W P hP := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  rw [smoothIntegralPointSection_inclusion]
  apply integralPointSection_unique A W P
  · exact (Category.assoc _ _ _).trans hs
  · rw [← Category.assoc, hg, projectiveToSmooth_inclusion]

end FLT.Mazur.WeierstrassIntegralChart
