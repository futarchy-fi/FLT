/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOnePointLeading
public import FLT.Mazur.SectionPoleSplit

/-!
# Split positive pole steps on the original varying genus-one family

The original family supplies the vanishing needed for a split exact pole
filtration. Each quotient is the actual line restricted along its section.
No cohomology witness or compatible coordinate basis is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)

/-- Each positive pole step is split over the original affine base ring. -/
def relativePointPoleSplit (m : ℕ) (hm : 0 < m) :
    { e : ModuleRingH G.hom.appTop.hom
        (tensorPower (divisorLineBundle s.left.ker hI) (m + 1)) 0 ≃ₗ[Γ(S, ⊤)]
          ModuleRingH G.hom.appTop.hom (tensorPower (divisorLineBundle s.left.ker hI) m) 0 ×
            Γ(sectionPoleLine s.left hI (m + 1), ⊤) //
      divisorPowerRingStep G.hom.appTop.hom hI m =
        e.symm.toLinearMap.comp (LinearMap.inl _ _ _) ∧
      sectionPoleLeading G.hom s.left s.w hI m =
        (LinearMap.snd _ _ _).comp e.toLinearMap } := by
  letI := relative_pointPower_acyclic G hg s hI m hm 0
  exact sectionPoleSplit G.hom s.left s.w hI m

include hg in
/-- Every section of the actual base line lifts to the original positive pole module. -/
theorem relative_pointPole_leading_surjective (m : ℕ) (hm : 0 < m) :
    Function.Surjective (sectionPoleLeading G.hom s.left s.w hI m) := by
  let _ := relative_pointPower_acyclic G hg s hI m hm 0
  exact sectionPoleLeading_surjective G.hom s.left s.w hI m

include hg in
/-- The relative positive pole quotient is an invertible base module. -/
theorem relative_pointPole_quotient_invertible (m : ℕ) (hm : 0 < m) :
    Module.Invertible Γ(S, ⊤)
      (ModuleRingH G.hom.appTop.hom
        (tensorPower (divisorLineBundle s.left.ker hI) (m + 1)) 0 ⧸
          LinearMap.range (divisorPowerRingStep G.hom.appTop.hom hI m)) := by
  let _ := relative_pointPower_acyclic G hg s hI m hm 0
  let _ := sectionPoleLine_sections_invertible (S := S) s.left hI (m + 1)
  exact Module.Invertible.congr
    (sectionPoleQuotientEquiv G.hom s.left s.w hI m).symm

end FLT.Mazur.FCurve
