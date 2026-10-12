/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOnePointSections
public import FLT.Mazur.DivisorPowerRingLeadingClass

/-!
# Lifting leading classes in the original relative pole filtration

The actual relative H¹ vanishing makes every positive leading class lift.
The quotient identification retains the original divisor transition and
base scalars, supplying the exact sequence needed for adapted local frames.
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

include hg in
/-- Every positive leading class on the original family lifts over its base ring. -/
theorem relative_pointPower_leading_surjective (m : ℕ) (hm : 0 < m) :
    Function.Surjective (divisorPowerRingLeading G.hom.appTop.hom hI m) := by
  let _ := relative_pointPower_acyclic G hg s hI m hm 0
  exact divisorPowerRingLeading_surjective G.hom.appTop.hom hI m

/-- The original relative positive pole quotient is the actual divisor quotient's sections. -/
def relativePointPowerLeadingEquiv (m : ℕ) (hm : 0 < m) :
    (ModuleRingH G.hom.appTop.hom (tensorPower (divisorLineBundle s.left.ker hI) (m + 1)) 0 ⧸
      LinearMap.range (divisorPowerRingStep G.hom.appTop.hom hI m)) ≃ₗ[Γ(S, ⊤)]
        ModuleRingH G.hom.appTop.hom (divisorTwistedComplex hI
          (tensorPower (divisorLineBundle s.left.ker hI) m)).X₃ 0 := by
  letI := relative_pointPower_acyclic G hg s hI m hm 0
  exact divisorPowerRingLeadingEquiv G.hom.appTop.hom hI m

end FLT.Mazur.FCurve
